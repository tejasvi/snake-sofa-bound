import Sofa3D.Crossing

/-!
# Proposition 4.5, Theorem 1.1, Corollary 5.1

The core (`prop45_core`) assumes that the rotation of the motion at time `0` is the identity and that the body
lies in `X`; `reduce_start` (Crossing.lean) reduces the general weak passage to this case.
-/

open MeasureTheory Set Filter Topology

namespace Sofa3D

/-- `μ*(u) = (u² − 2)/(u² + 2)`. -/
noncomputable def muStar (u : ℝ) : ℝ := (u ^ 2 - 2) / (u ^ 2 + 2)

lemma muStar_lt_one (u : ℝ) : muStar u < 1 := by
  unfold muStar; rw [div_lt_one (by positivity)]; linarith

/-- The unit vectors `e_x`, `e_y`, `e_z`. -/
def ex : Fin 3 → ℝ := ![1, 0, 0]
def ey : Fin 3 → ℝ := ![0, 1, 0]
def ez : Fin 3 → ℝ := ![0, 0, 1]
/-- Base points of `X` and `Y`. -/
noncomputable def ρX : Fin 3 → ℝ := ![0, 1 / 2, 1 / 2]
noncomputable def ρY : Fin 3 → ℝ := ![1 / 2, 0, 1 / 2]

lemma Xt_tube : Xt = tube ρX ex ey ez := Xt_eq
lemma Yt_tube : Yt = tube ρY ey ex ez := Yt_eq
lemma orth_X : Orthonormal3 ex ey ez := orthonormal_xyz
lemma orth_Y : Orthonormal3 ey ex ez := orthonormal_yxz

lemma dot_ex (w : Fin 3 → ℝ) : dotProduct w ex = w 0 := by
  simp only [dotProduct_fin3, ex, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]; ring
lemma dot_ey (w : Fin 3 → ℝ) : dotProduct w ey = w 1 := by
  simp only [dotProduct_fin3, ey, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]; ring

/-- A tube with axis direction `w` meets `X` in volume at most `1/√(1 − w₀²)` (when `|w₀| < 1`). -/
lemma vol_tube_inter_X {ρ w f₁ f₂ : Fin 3 → ℝ} (h : Orthonormal3 w f₁ f₂) (hw : |w 0| < 1) :
    volume (tube ρ w f₁ f₂ ∩ Xt) ≤ ENNReal.ofReal (1 / Real.sqrt (1 - (w 0) ^ 2)) := by
  rw [Xt_tube]
  have := two_tube ρ w f₁ f₂ ρX ex ey ez h orth_X (by rw [dot_ex]; exact hw)
  rwa [dot_ex] at this

lemma vol_tube_inter_Y {ρ w f₁ f₂ : Fin 3 → ℝ} (h : Orthonormal3 w f₁ f₂) (hw : |w 1| < 1) :
    volume (tube ρ w f₁ f₂ ∩ Yt) ≤ ENNReal.ofReal (1 / Real.sqrt (1 - (w 1) ^ 2)) := by
  rw [Yt_tube]
  have := two_tube ρ w f₁ f₂ ρY ey ex ez h orth_Y (by rw [dot_ey]; exact hw)
  rwa [dot_ey] at this

lemma isClosed_body {B : Set (Fin 3 → ℝ)} (hB : IsBody B) : IsClosed B := hB.1.isClosed

set_option maxHeartbeats 2000000 in
/-- **Proposition 4.5 (core).** -/
theorem prop45_core {M u s : ℝ} (hu : Real.sqrt 2 < u) (huM : u < M) (hs : 0 < s) (hsu : s ≤ muStar u)
    {B : Set (Fin 3 → ℝ)} (hB : IsBody B) {g : unitInterval → Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)}
    (hg : IsWeakPassage M B g) (hg0 : (g 0).1 = 1) (hBX : B ⊆ Xt) :
    volume B ≤ ENNReal.ofReal (1 / s + 1 / Real.sqrt (1 - s ^ 2)) := by
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hu0 : 0 < u := hs2.trans hu
  have hM : 0 < M := hu0.trans huM
  have hs1 : s < 1 := hsu.trans_lt (muStar_lt_one u)
  have hBne : B.Nonempty := hB.2.nonempty
  have hBm : MeasurableSet B := (isClosed_body hB).measurableSet
  -- the motion on ℝ
  set G : ℝ → Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ) := Set.IccExtend zero_le_one g with hGdef
  have hG : Continuous G := continuous_IccExtend_iff.mpr hg.continuous
  have hGt : ∀ t (ht : t ∈ Icc (0 : ℝ) 1), G t = g ⟨t, ht⟩ := fun t ht => Set.IccExtend_of_mem _ _ ht
  have hG0 : G 0 = g 0 := hGt 0 ⟨le_refl _, zero_le_one⟩
  have hG1 : G 1 = g 1 := hGt 1 ⟨zero_le_one, le_refl _⟩
  have hrot : ∀ t ∈ Icc (0 : ℝ) 1, (G t).1 ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    intro t ht; rw [hGt t ht]; exact hg.rotation _
  have hinside : ∀ t ∈ Icc (0 : ℝ) 1, motion (G t) '' B ⊆ corridor M := by
    intro t ht; rw [hGt t ht]; exact hg.inside _
  have hmot : Continuous fun x : ℝ × (Fin 3 → ℝ) => motion (G x.1) x.2 :=
    continuous_motion_joint.comp ((hG.comp continuous_fst).prodMk continuous_snd)
  have hmott : ∀ t, Continuous (motion (G t)) := fun t =>
    hmot.comp (continuous_const.prodMk continuous_id)
  -- volume of every position
  have hvol : ∀ t ∈ Icc (0 : ℝ) 1, volume (motion (G t) '' B) = volume B :=
    fun t ht => volume_motion_image _ (hrot t ht) hBm
  -- the tube at time t
  set w : ℝ → (Fin 3 → ℝ) := fun t => Matrix.mulVec (G t).1 ex with hw
  have horth : ∀ t ∈ Icc (0 : ℝ) 1,
      Orthonormal3 (w t) (Matrix.mulVec (G t).1 ey) (Matrix.mulVec (G t).1 ez) :=
    fun t ht => orth_X.mulVec (SO_transpose_mul (hrot t ht))
  have hsubT : ∀ t, motion (G t) '' B ⊆
      tube (motion (G t) ρX) (w t) (Matrix.mulVec (G t).1 ey) (Matrix.mulVec (G t).1 ez) := by
    intro t
    rw [← motion_image_tube, ← Xt_tube]
    exact image_mono hBX
  have hwunit : ∀ t ∈ Icc (0 : ℝ) 1, w t 0 ^ 2 + w t 1 ^ 2 + w t 2 ^ 2 = 1 := by
    intro t ht
    have := (horth t ht).1
    rw [dotProduct_fin3] at this; linear_combination this
  -- the height function
  set ht : ℝ → ℝ := fun t => sSup ((fun q => motion (G t) q 1) '' B) with hht
  have hhtc : Continuous ht :=
    hB.1.continuous_sSup (f := fun t q => motion (G t) q 1) ((continuous_apply 1).comp hmot)
  have hbdd : ∀ t, BddAbove ((fun q => motion (G t) q 1) '' B) := fun t =>
    hB.1.bddAbove_image (((continuous_apply 1).comp (hmott t)).continuousOn)
  have hle_ht : ∀ t, ∀ q ∈ B, motion (G t) q 1 ≤ ht t := fun t q hq =>
    le_csSup (hbdd t) (mem_image_of_mem _ hq)
  have hht0 : ht 0 ≤ 1 := by
    apply csSup_le (hBne.image _)
    rintro _ ⟨q, hq, rfl⟩
    have := hg.start (mem_image_of_mem _ hq)
    rw [hG0]; exact this.2
  have hht1 : 1 + M ≤ ht 1 := by
    obtain ⟨p, ⟨q, hq, rfl⟩, hp⟩ := hg.finish
    rw [← hG1] at hp
    exact hp.trans (hle_ht 1 q hq)
  -- the first crossing time τ
  set c := 1 + u with hc
  have hc1 : 1 < c := by linarith
  have hcM : c < 1 + M := by linarith
  set S := {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ c ≤ ht t} with hS
  have hSc : IsClosed S := isClosed_Icc.inter (isClosed_le continuous_const hhtc)
  have hS1 : (1 : ℝ) ∈ S := ⟨⟨zero_le_one, le_refl _⟩, by linarith⟩
  have hSne : S.Nonempty := ⟨1, hS1⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht' => ht'.1.1⟩
  set τ := sInf S with hτ
  have hτS : τ ∈ S := hSc.csInf_mem hSne hSbdd
  have hτ0 : 0 ≤ τ := hτS.1.1
  have hτ1 : τ ≤ 1 := hτS.1.2
  have hτI : τ ∈ Icc (0 : ℝ) 1 := hτS.1
  have hhtτ : ht τ = c := by
    obtain ⟨t', ht'I, ht'v⟩ := intermediate_value_Icc hτ0 hhtc.continuousOn
      ⟨by linarith, hτS.2⟩
    have ht'S : t' ∈ S := ⟨⟨ht'I.1, ht'I.2.trans hτ1⟩, ht'v.ge⟩
    have : τ ≤ t' := csInf_le hSbdd ht'S
    have : t' = τ := le_antisymm ht'I.2 this
    rw [← this]; exact ht'v
  have hhtle : ∀ t ∈ Icc 0 τ, ht t ≤ c := by
    intro t htI
    rcases eq_or_lt_of_le htI.2 with h | h
    · rw [h, hhtτ]
    · by_contra hcon
      push Not at hcon
      have : t ∈ S := ⟨⟨htI.1, htI.2.trans hτ1⟩, hcon.le⟩
      exact absurd (csInf_le hSbdd this) (not_le.mpr h)
  have hIτ : ∀ t ∈ Icc 0 τ, t ∈ Icc (0 : ℝ) 1 := fun t htI => ⟨htI.1, htI.2.trans hτ1⟩
  -- B_t ⊆ S_X ∪ S_Y(c) for t ≤ τ
  have hlow : ∀ t ∈ Icc 0 τ, motion (G t) '' B ⊆ SX ∪ SYc c := by
    rintro t htI _ ⟨q, hq, rfl⟩
    exact corridor_le hcM (hinside t (hIτ t htI) (mem_image_of_mem _ hq))
      ((hle_ht t q hq).trans (hhtle t htI))
  have hlowXY : ∀ t ∈ Icc 0 τ, motion (G t) '' B ⊆ Xt ∪ Yt := fun t htI =>
    (hlow t htI).trans (union_subset_union SX_sub_Xt (SYc_sub_Yt c))
  -- a point of W_c in B_τ
  obtain ⟨q, hqB, hqW⟩ : ∃ q ∈ motion (G τ) '' B, q ∈ W c := by
    have hK : IsCompact ((fun q => motion (G τ) q 1) '' B) :=
      hB.1.image ((continuous_apply 1).comp (hmott τ))
    obtain ⟨q₀, hq₀, hq₀v⟩ := hK.sSup_mem (hBne.image _)
    refine ⟨motion (G τ) q₀, mem_image_of_mem _ hq₀, ?_⟩
    have hy : motion (G τ) q₀ 1 = c := by rw [← hhtτ]; exact hq₀v
    rcases hlow τ ⟨hτ0, le_refl _⟩ (mem_image_of_mem _ hq₀) with h | h
    · exact absurd h.2.2.1 (by rw [hy]; linarith)
    · exact ⟨h.1, h.2.1, hy, h.2.2.2.2.1, h.2.2.2.2.2⟩
  -- the angle function
  set μ : ℝ → ℝ := fun t => |w t 1| with hμ
  have hμc : Continuous μ := by
    have : Continuous w := (hG.fst).matrix_mulVec continuous_const
    exact ((continuous_apply 1).comp this).abs
  have hμ0 : μ 0 = 0 := by
    simp only [hμ, hw, hG0, hg0, Matrix.one_mulVec]
    simp [ex]
  -- an angle exactly s at some time t ≤ τ gives the bound
  have hbound_final : ∀ t ∈ Icc 0 τ, μ t = s →
      volume B ≤ ENNReal.ofReal (1 / s + 1 / Real.sqrt (1 - s ^ 2)) := by
    intro t htI hμt
    have htI1 := hIτ t htI
    have hwt := hwunit t htI1
    have hμt' : |w t 1| = s := hμt
    have h1sq : w t 1 ^ 2 = s ^ 2 := by rw [← sq_abs, hμt']
    have h0sq : w t 0 ^ 2 ≤ 1 - s ^ 2 := by nlinarith [sq_nonneg (w t 2)]
    have hw0 : |w t 0| < 1 := by
      rw [← sq_lt_one_iff_abs_lt_one]; nlinarith
    have hw1 : |w t 1| < 1 := by rw [hμt']; exact hs1
    have hs2pos : 0 < 1 - s ^ 2 := by nlinarith
    rw [← hvol t htI1]
    calc volume (motion (G t) '' B)
        ≤ volume ((tube (motion (G t) ρX) (w t) (Matrix.mulVec (G t).1 ey) (Matrix.mulVec (G t).1 ez) ∩ Xt) ∪
            (tube (motion (G t) ρX) (w t) (Matrix.mulVec (G t).1 ey) (Matrix.mulVec (G t).1 ez) ∩ Yt)) := by
          apply measure_mono
          intro p hp
          have hT := hsubT t hp
          rcases hlowXY t htI hp with h | h
          · exact Or.inl ⟨hT, h⟩
          · exact Or.inr ⟨hT, h⟩
      _ ≤ volume (tube (motion (G t) ρX) (w t) (Matrix.mulVec (G t).1 ey) (Matrix.mulVec (G t).1 ez) ∩ Xt) +
            volume (tube (motion (G t) ρX) (w t) (Matrix.mulVec (G t).1 ey) (Matrix.mulVec (G t).1 ez) ∩ Yt) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (1 / Real.sqrt (1 - (w t 0) ^ 2)) +
            ENNReal.ofReal (1 / Real.sqrt (1 - (w t 1) ^ 2)) :=
          add_le_add (vol_tube_inter_X (horth t htI1) hw0) (vol_tube_inter_Y (horth t htI1) hw1)
      _ ≤ ENNReal.ofReal (1 / s) + ENNReal.ofReal (1 / Real.sqrt (1 - s ^ 2)) := by
          rw [h1sq]
          gcongr
          rw [show s = Real.sqrt (s ^ 2) from (Real.sqrt_sq hs.le).symm]
          exact Real.sqrt_le_sqrt (by linarith)
      _ = ENNReal.ofReal (1 / s + 1 / Real.sqrt (1 - s ^ 2)) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  -- reaching the angle s at time τ suffices (intermediate values of μ on [0, τ])
  have hfromμτ : s ≤ μ τ → volume B ≤ ENNReal.ofReal (1 / s + 1 / Real.sqrt (1 - s ^ 2)) := by
    intro hsτ
    obtain ⟨t, htI, hμt⟩ := intermediate_value_Icc hτ0 hμc.continuousOn ⟨by rw [hμ0]; exact hs.le, hsτ⟩
    exact hbound_final t htI hμt
  by_cases hA : ∃ p ∈ motion (G τ) '' B, p 1 ≤ 1
  · -- a point of W₁ in B_τ, by connectedness; then the tilt lemma
    apply hfromμτ
    have hconn : IsPreconnected (motion (G τ) '' B) :=
      (hB.2.image _ (hmott τ).continuousOn).isPreconnected
    set A₂ := motion (G τ) '' B ∩ {p | 1 < p 1} with hA₂
    obtain ⟨p, hpB, hp1, hpcl⟩ := isPreconnected_closed_iff.mp hconn {p | p 1 ≤ 1} (closure A₂)
      (isClosed_le (continuous_apply 1) continuous_const) isClosed_closure
      (fun p hp => by
        by_cases h : p 1 ≤ 1
        · exact Or.inl h
        · exact Or.inr (subset_closure ⟨hp, not_le.mp h⟩))
      (let ⟨p, hp, hp1⟩ := hA; ⟨p, hp, hp1⟩)
      ⟨q, hqB, subset_closure ⟨hqB, by
        show 1 < q 1
        rw [hqW.2.2.1]; exact hc1⟩⟩
    have hclos : closure A₂ ⊆
        {p : Fin 3 → ℝ | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 1 ≤ p 1 ∧ 0 ≤ p 2 ∧ p 2 ≤ 1} := by
      apply closure_minimal
      · rintro p ⟨hpB', hp1'⟩
        rcases hlow τ ⟨hτ0, le_refl _⟩ hpB' with h | h
        · exact absurd h.2.2.1 (not_le.mpr hp1')
        · exact ⟨h.1, h.2.1, le_of_lt hp1', h.2.2.2.2.1, h.2.2.2.2.2⟩
      · simp only [Set.setOf_and]
        exact (isClosed_le continuous_const (continuous_apply 0)).inter
          ((isClosed_le (continuous_apply 0) continuous_const).inter
          ((isClosed_le continuous_const (continuous_apply 1)).inter
          ((isClosed_le continuous_const (continuous_apply 2)).inter
          (isClosed_le (continuous_apply 2) continuous_const))))
    obtain ⟨h0, h1, h2, h3, h4⟩ := hclos hpcl
    have hpW : p ∈ W 1 := ⟨h0, h1, le_antisymm hp1 h2, h3, h4⟩
    have hqW' : q ∈ W (1 + u) := hqW
    exact hsu.trans (tilt hu (horth τ hτI) (hsubT τ hpB) (hsubT τ hqB) hpW hqW')
  · push Not at hA
    by_cases hsτ : s ≤ μ τ
    · exact hfromμτ hsτ
    · push Not at hsτ
      have hBY : motion (G τ) '' B ⊆ Yt := by
        intro p hp
        rcases hlow τ ⟨hτ0, le_refl _⟩ hp with h | h
        · exact absurd h.2.2.1 (not_le.mpr (hA p hp))
        · exact SYc_sub_Yt c h
      have hsτ' : |w τ 1| < s := hsτ
      have hw1 : |w τ 1| < 1 := hsτ'.trans hs1
      have hs2pos : 0 < 1 - s ^ 2 := by nlinarith
      have hsq : w τ 1 ^ 2 ≤ s ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hsτ'.le 2
      rw [← hvol τ hτI]
      calc volume (motion (G τ) '' B)
          ≤ volume (tube (motion (G τ) ρX) (w τ) (Matrix.mulVec (G τ).1 ey) (Matrix.mulVec (G τ).1 ez) ∩ Yt) :=
            measure_mono (fun p hp => ⟨hsubT τ hp, hBY hp⟩)
        _ ≤ ENNReal.ofReal (1 / Real.sqrt (1 - (w τ 1) ^ 2)) := vol_tube_inter_Y (horth τ hτI) hw1
        _ ≤ ENNReal.ofReal (1 / Real.sqrt (1 - s ^ 2)) := by
            apply ENNReal.ofReal_le_ofReal
            apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr hs2pos)
            exact Real.sqrt_le_sqrt (by linarith)
        _ ≤ ENNReal.ofReal (1 / s + 1 / Real.sqrt (1 - s ^ 2)) := by
            apply ENNReal.ofReal_le_ofReal
            have : 0 < 1 / s := one_div_pos.mpr hs
            linarith

/-- **Proposition 4.5.** -/
theorem prop45 {M u s : ℝ} (hu : Real.sqrt 2 < u) (huM : u < M) (hs : 0 < s) (hsu : s ≤ muStar u)
    {B : Set (Fin 3 → ℝ)} (hB : IsBody B) {g : unitInterval → Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)}
    (hg : IsWeakPassage M B g) :
    volume B ≤ ENNReal.ofReal (1 / s + 1 / Real.sqrt (1 - s ^ 2)) := by
  have hM : 0 < M := (Real.sqrt_nonneg 2).trans_lt (hu.trans huM)
  obtain ⟨hg', hg0', himg⟩ := reduce_start hg
  have hB₀ : IsBody (motion (g 0) '' B) := isBody_image hB _
  have hB₀X : motion (g 0) '' B ⊆ Xt := fun p hp =>
    corridor_le_one_sub_Xt hM (hg.start hp).1 (hg.start hp).2
  have hvol : volume (motion (g 0) '' B) = volume B :=
    volume_motion_image _ (hg.rotation 0) (isClosed_body hB).measurableSet
  rw [← hvol]
  exact prop45_core hu huM hs hsu hB₀ hg' hg0' hB₀X

/-- A passage is a weak passage. -/
lemma IsPassage.weak {M : ℝ} {B : Set (Fin 3 → ℝ)} {g : unitInterval → Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)}
    (hB : IsBody B) (hg : IsPassage M B g) : IsWeakPassage M B g := by
  refine ⟨hg.continuous, hg.rotation, hg.inside, fun p hp => ⟨Or.inl (Or.inl (hg.start hp)), (hg.start hp).2.2.1⟩, ?_⟩
  obtain ⟨b, hb⟩ := hB.2.nonempty
  exact ⟨_, mem_image_of_mem _ hb, (hg.finish (mem_image_of_mem _ hb)).2.2.1⟩

lemma muStar_two_add_sqrt_two : muStar (2 + Real.sqrt 2) = 1 / Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := by positivity
  unfold muStar
  rw [div_eq_div_iff (by nlinarith) hpos.ne']
  nlinarith

lemma bound_at_half : 1 / (1 / Real.sqrt 2) + 1 / Real.sqrt (1 - (1 / Real.sqrt 2) ^ 2) = 2 * Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := by positivity
  have h3 : 1 - (1 / Real.sqrt 2) ^ 2 = (1 / Real.sqrt 2) ^ 2 := by
    rw [div_pow, h2]; norm_num
  rw [h3, Real.sqrt_sq (by positivity)]
  field_simp
  ring

/-- **Theorem 1.1 for weak passages.** -/
theorem weak : WeakStatement := by
  intro M hM B g hB hg
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have := prop45 (u := 2 + Real.sqrt 2) (s := 1 / Real.sqrt 2) (by linarith) hM (by positivity)
    (by rw [muStar_two_add_sqrt_two]) hB hg
  rwa [bound_at_half] at this

/-- **Theorem 1.1.** -/
theorem main : MainStatement := by
  intro M hM
  apply iSup_le; intro B; apply iSup_le; intro hB; apply iSup_le; rintro ⟨g, hg⟩
  exact weak M hM B g hB (hg.weak hB)

/-- `1/μ*(u) + 1/√(1 − μ*(u)²) = Γ(u)` for `u > √2`. -/
lemma bound_eq_Gamma {u : ℝ} (hu : Real.sqrt 2 < u) :
    1 / muStar u + 1 / Real.sqrt (1 - muStar u ^ 2) = Gamma u := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hu0 : 0 < u := hs2.trans hu
  have hu2 : 2 < u ^ 2 := by nlinarith
  have hsq : 1 - muStar u ^ 2 = (2 * Real.sqrt 2 * u / (u ^ 2 + 2)) ^ 2 := by
    unfold muStar
    rw [div_pow, div_pow, mul_pow, mul_pow, h2]
    field_simp
    ring
  rw [hsq, Real.sqrt_sq (by positivity)]
  unfold muStar Gamma
  field_simp

lemma continuousAt_Gamma {M : ℝ} (hM : Real.sqrt 2 < M) : ContinuousAt Gamma M := by
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hM0 : 0 < M := hs2.trans hM
  have hM2 : M ^ 2 - 2 ≠ 0 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith
  unfold Gamma
  apply ContinuousAt.add
  · exact ContinuousAt.div (by fun_prop) (by fun_prop) hM2
  · exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)

/-- **Corollary 5.1** for weak passages. -/
theorem weak_short {M : ℝ} (hM : Real.sqrt 2 < M) {B : Set (Fin 3 → ℝ)} (hB : IsBody B)
    {g : unitInterval → Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)} (hg : IsWeakPassage M B g) :
    volume B ≤ ENNReal.ofReal (Gamma M) := by
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hlim : Filter.Tendsto (fun u => ENNReal.ofReal (Gamma u)) (𝓝[<] M) (𝓝 (ENNReal.ofReal (Gamma M))) :=
    ((ENNReal.continuous_ofReal.tendsto _).comp (continuousAt_Gamma hM)).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hM] with u hu
  have hu2 : 2 < u ^ 2 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [hu.1]
  have hs : 0 < muStar u := by unfold muStar; apply div_pos <;> linarith
  have := prop45 hu.1 hu.2 hs le_rfl hB hg
  rwa [bound_eq_Gamma hu.1] at this

/-- **Corollary 5.1.** -/
theorem short : ShortStatement := by
  intro M hM _
  apply iSup_le; intro B; apply iSup_le; intro hB; apply iSup_le; rintro ⟨g, hg⟩
  exact weak_short hM hB (hg.weak hB)

lemma Gamma_two_add_sqrt_two : Gamma (2 + Real.sqrt 2) = 2 * Real.sqrt 2 := by
  have hs2 : 0 < Real.sqrt 2 := by positivity
  rw [← bound_eq_Gamma (by linarith), muStar_two_add_sqrt_two, bound_at_half]

/-- **Remark 5.2(a).** Theorem 1.1 also holds for `M = 2 + √2`. -/
theorem main_ge (M : ℝ) (hM : 2 + Real.sqrt 2 ≤ M) : Vstar M ≤ ENNReal.ofReal (2 * Real.sqrt 2) := by
  rcases eq_or_lt_of_le hM with h | h
  · subst h
    have := short (2 + Real.sqrt 2) (by have := Real.sqrt_nonneg 2; linarith) le_rfl
    rwa [Gamma_two_add_sqrt_two] at this
  · exact main M h

end Sofa3D
