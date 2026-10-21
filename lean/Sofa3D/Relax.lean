import Sofa3D.Extras

/-!
# Proposition 6.1: the value of the one-time relaxation

For `0 < s < 1` and `c ≥ 1 + (1 + s)/√(1 − s²)`, every tube whose axis direction `w` has `|w · e_y| = s` meets
`S_X ∪ S_Y(c)` in volume at most `1/s + 1/√(1 − s²)`, and the tube
`T = {p : 0 ≤ (p − e_y) · n ≤ 1, 0 ≤ p · e_z ≤ 1}`, `n = (−s, κ, 0)`, `κ = √(1 − s²)`, attains this value.
-/

open MeasureTheory Set

namespace Sofa3D

/-- The upper bound of Proposition 6.1. -/
theorem relax_upper {s c : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ρ e f₁ f₂ : Fin 3 → ℝ} (h : Orthonormal3 e f₁ f₂)
    (he : |e 1| = s) :
    volume (tube ρ e f₁ f₂ ∩ (SX ∪ SYc c)) ≤ ENNReal.ofReal (1 / s + 1 / Real.sqrt (1 - s ^ 2)) := by
  have hunit : e 0 ^ 2 + e 1 ^ 2 + e 2 ^ 2 = 1 := by
    have := h.1; rw [dotProduct_fin3] at this; linear_combination this
  have h1sq : e 1 ^ 2 = s ^ 2 := by rw [← sq_abs, he]
  have h0sq : e 0 ^ 2 ≤ 1 - s ^ 2 := by nlinarith [sq_nonneg (e 2)]
  have hs2pos : 0 < 1 - s ^ 2 := by nlinarith
  have hw0 : |e 0| < 1 := by rw [← sq_lt_one_iff_abs_lt_one]; nlinarith
  have hw1 : |e 1| < 1 := by rw [he]; exact hs1
  calc volume (tube ρ e f₁ f₂ ∩ (SX ∪ SYc c))
      ≤ volume ((tube ρ e f₁ f₂ ∩ Xt) ∪ (tube ρ e f₁ f₂ ∩ Yt)) := by
        apply measure_mono
        rintro p ⟨hT, hp | hp⟩
        · exact Or.inl ⟨hT, SX_sub_Xt hp⟩
        · exact Or.inr ⟨hT, SYc_sub_Yt c hp⟩
    _ ≤ volume (tube ρ e f₁ f₂ ∩ Xt) + volume (tube ρ e f₁ f₂ ∩ Yt) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (1 / Real.sqrt (1 - (e 0) ^ 2)) + ENNReal.ofReal (1 / Real.sqrt (1 - (e 1) ^ 2)) :=
        add_le_add (vol_tube_inter_X h hw0) (vol_tube_inter_Y h hw1)
    _ ≤ ENNReal.ofReal (1 / s) + ENNReal.ofReal (1 / Real.sqrt (1 - s ^ 2)) := by
        rw [h1sq]
        gcongr
        rw [show s = Real.sqrt (s ^ 2) from (Real.sqrt_sq hs0.le).symm]
        exact Real.sqrt_le_sqrt (by linarith)
    _ = ENNReal.ofReal (1 / s + 1 / Real.sqrt (1 - s ^ 2)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm

section Extremal

variable (s : ℝ)

/-- `κ = √(1 − s²)`. -/
noncomputable def kap : ℝ := Real.sqrt (1 - s ^ 2)
/-- The axis `w = (κ, s, 0)`, the normal `n = (−s, κ, 0)`, and the base point `e_y + n/2 + e_z/2`. -/
noncomputable def wAx : Fin 3 → ℝ := ![kap s, s, 0]
noncomputable def nAx : Fin 3 → ℝ := ![-s, kap s, 0]
noncomputable def ρAx : Fin 3 → ℝ := ![-s / 2, 1 + kap s / 2, 1 / 2]

/-- The extremal tube. -/
noncomputable def Tex : Set (Fin 3 → ℝ) := tube (ρAx s) (wAx s) (nAx s) ez

variable {s}

lemma kap_sq (hs1 : s < 1) (hs0 : 0 < s) : kap s ^ 2 = 1 - s ^ 2 := Real.sq_sqrt (by nlinarith)

lemma kap_pos (hs1 : s < 1) (hs0 : 0 < s) : 0 < kap s := Real.sqrt_pos.mpr (by nlinarith)

lemma orth_ex (hs1 : s < 1) (hs0 : 0 < s) : Orthonormal3 (wAx s) (nAx s) ez := by
  have hk := kap_sq hs1 hs0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [dotProduct_fin3, wAx, nAx, ez, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;> nlinarith

lemma mem_Tex (hs1 : s < 1) (hs0 : 0 < s) (p : Fin 3 → ℝ) :
    p ∈ Tex s ↔ (0 ≤ (p 1 - 1) * kap s - p 0 * s ∧ (p 1 - 1) * kap s - p 0 * s ≤ 1) ∧
      (0 ≤ p 2 ∧ p 2 ≤ 1) := by
  rw [Tex, mem_tube_iff (orth_ex hs1 hs0)]
  have hk := kap_sq hs1 hs0
  simp only [dotProduct_fin3, Pi.sub_apply, nAx, ez, ρAx, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have e1 : (p 0 - -s / 2) * -s + (p 1 - (1 + kap s / 2)) * kap s + (p 2 - 1 / 2) * 0 =
      ((p 1 - 1) * kap s - p 0 * s) - 1 / 2 := by nlinarith
  have e2 : (p 0 - -s / 2) * 0 + (p 1 - (1 + kap s / 2)) * 0 + (p 2 - 1 / 2) * 1 = p 2 - 1 / 2 := by ring
  rw [e1, e2, abs_le, abs_le]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

lemma Tex_inter_Xt (hs1 : s < 1) (hs0 : 0 < s) :
    Tex s ∩ Xt = {p | (0 ≤ (p 1 - 1) * kap s - p 0 * s ∧ (p 1 - 1) * kap s - p 0 * s ≤ 1) ∧
      (0 ≤ p 1 ∧ p 1 ≤ 1) ∧ (0 ≤ p 2 ∧ p 2 ≤ 1)} := by
  ext p; rw [mem_inter_iff, mem_Tex hs1 hs0]
  simp only [Xt, mem_ofPred_eq]; tauto

lemma Tex_inter_Yt (hs1 : s < 1) (hs0 : 0 < s) :
    Tex s ∩ Yt = {p | (0 ≤ (p 1 - 1) * kap s - p 0 * s ∧ (p 1 - 1) * kap s - p 0 * s ≤ 1) ∧
      (0 ≤ p 0 ∧ p 0 ≤ 1) ∧ (0 ≤ p 2 ∧ p 2 ≤ 1)} := by
  ext p; rw [mem_inter_iff, mem_Tex hs1 hs0]
  simp only [Yt, mem_ofPred_eq]; tauto

lemma framePsi_xyz (g σ l : ℝ) : framePsi 0 ex ey ez (g, σ, l) = ![l, σ, g] := by
  funext i; fin_cases i <;> simp [framePsi, ex, ey, ez]

lemma framePsi_yxz (g σ l : ℝ) : framePsi 0 ey ex ez (g, σ, l) = ![σ, l, g] := by
  funext i; fin_cases i <;> simp [framePsi, ex, ey, ez]

lemma lintegral_box (L : ENNReal) :
    ∫⁻ g, ∫⁻ σ, (Icc (0 : ℝ) 1).indicator (fun _ => (Icc (0 : ℝ) 1).indicator (fun _ => L) g) σ = L := by
  simp_rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
    mul_one]
  rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

lemma measurableSet_halfspaces {f₁ f₂ f₃ : (Fin 3 → ℝ) → ℝ} (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (h₃ : Continuous f₃) :
    MeasurableSet {p | (0 ≤ f₁ p ∧ f₁ p ≤ 1) ∧ (0 ≤ f₂ p ∧ f₂ p ≤ 1) ∧ (0 ≤ f₃ p ∧ f₃ p ≤ 1)} := by
  apply IsClosed.measurableSet
  simp only [Set.setOf_and]
  exact ((isClosed_le continuous_const h₁).inter (isClosed_le h₁ continuous_const)).inter
    (((isClosed_le continuous_const h₂).inter (isClosed_le h₂ continuous_const)).inter
    ((isClosed_le continuous_const h₃).inter (isClosed_le h₃ continuous_const)))

lemma vol_Tex_X (hs1 : s < 1) (hs0 : 0 < s) : volume (Tex s ∩ Xt) = ENNReal.ofReal (1 / s) := by
  rw [Tex_inter_Xt hs1 hs0]
  rw [volume_eq_iter orth_X 0 (measurableSet_halfspaces (by fun_prop) (by fun_prop) (by fun_prop))]
  have hin : ∀ g σ : ℝ, volume {l : ℝ | framePsi 0 ex ey ez (g, σ, l) ∈
      {p : Fin 3 → ℝ | (0 ≤ (p 1 - 1) * kap s - p 0 * s ∧ (p 1 - 1) * kap s - p 0 * s ≤ 1) ∧
        (0 ≤ p 1 ∧ p 1 ≤ 1) ∧ (0 ≤ p 2 ∧ p 2 ≤ 1)}} =
      (Icc (0 : ℝ) 1).indicator (fun _ => (Icc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (1 / s)) g) σ := by
    intro g σ
    simp only [framePsi_xyz, mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    by_cases hσ : σ ∈ Icc (0 : ℝ) 1
    · by_cases hg : g ∈ Icc (0 : ℝ) 1
      · rw [indicator_of_mem hσ, indicator_of_mem hg]
        have : {l : ℝ | (0 ≤ (σ - 1) * kap s - l * s ∧ (σ - 1) * kap s - l * s ≤ 1) ∧
            (0 ≤ σ ∧ σ ≤ 1) ∧ (0 ≤ g ∧ g ≤ 1)} = Icc (((σ - 1) * kap s - 1) / s) (((σ - 1) * kap s) / s) := by
          ext l
          simp only [mem_ofPred_eq, mem_Icc, hσ.1, hσ.2, hg.1, hg.2, and_self, and_true]
          rw [div_le_iff₀ hs0, le_div_iff₀ hs0]
          constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
        rw [this, Real.volume_Icc]
        congr 1; field_simp; ring
      · rw [indicator_of_mem hσ, indicator_of_notMem hg]
        exact measure_mono_null (fun l hl => hg ⟨hl.2.2.1, hl.2.2.2⟩) measure_empty
    · rw [indicator_of_notMem hσ]
      exact measure_mono_null (fun l hl => hσ ⟨hl.2.1.1, hl.2.1.2⟩) measure_empty
  simp_rw [hin]
  exact lintegral_box _

lemma vol_Tex_Y (hs1 : s < 1) (hs0 : 0 < s) : volume (Tex s ∩ Yt) = ENNReal.ofReal (1 / kap s) := by
  have hk := kap_pos hs1 hs0
  rw [Tex_inter_Yt hs1 hs0]
  rw [volume_eq_iter orth_Y 0 (measurableSet_halfspaces (by fun_prop) (by fun_prop) (by fun_prop))]
  have hin : ∀ g σ : ℝ, volume {l : ℝ | framePsi 0 ey ex ez (g, σ, l) ∈
      {p : Fin 3 → ℝ | (0 ≤ (p 1 - 1) * kap s - p 0 * s ∧ (p 1 - 1) * kap s - p 0 * s ≤ 1) ∧
        (0 ≤ p 0 ∧ p 0 ≤ 1) ∧ (0 ≤ p 2 ∧ p 2 ≤ 1)}} =
      (Icc (0 : ℝ) 1).indicator (fun _ => (Icc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (1 / kap s)) g) σ := by
    intro g σ
    simp only [framePsi_yxz, mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    by_cases hσ : σ ∈ Icc (0 : ℝ) 1
    · by_cases hg : g ∈ Icc (0 : ℝ) 1
      · rw [indicator_of_mem hσ, indicator_of_mem hg]
        have : {l : ℝ | (0 ≤ (l - 1) * kap s - σ * s ∧ (l - 1) * kap s - σ * s ≤ 1) ∧
            (0 ≤ σ ∧ σ ≤ 1) ∧ (0 ≤ g ∧ g ≤ 1)} =
            Icc (1 + σ * s / kap s) (1 + (1 + σ * s) / kap s) := by
          ext l
          simp only [mem_ofPred_eq, mem_Icc, hσ.1, hσ.2, hg.1, hg.2, and_self, and_true]
          have e1 : 1 + σ * s / kap s ≤ l ↔ σ * s ≤ (l - 1) * kap s := by
            rw [← sub_nonneg, show l - (1 + σ * s / kap s) = ((l - 1) * kap s - σ * s) / kap s by
              field_simp; ring]
            rw [div_nonneg_iff]; constructor
            · rintro (⟨h1, _⟩ | ⟨_, h2⟩) <;> linarith
            · intro h; left; exact ⟨by linarith, hk.le⟩
          have e2 : l ≤ 1 + (1 + σ * s) / kap s ↔ (l - 1) * kap s ≤ 1 + σ * s := by
            rw [← sub_nonneg, show 1 + (1 + σ * s) / kap s - l = (1 + σ * s - (l - 1) * kap s) / kap s by
              field_simp; ring]
            rw [div_nonneg_iff]; constructor
            · rintro (⟨h1, _⟩ | ⟨_, h2⟩) <;> linarith
            · intro h; left; exact ⟨by linarith, hk.le⟩
          rw [e1, e2]
          constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
        rw [this, Real.volume_Icc]
        congr 1; field_simp; ring
      · rw [indicator_of_mem hσ, indicator_of_notMem hg]
        exact measure_mono_null (fun l hl => hg ⟨hl.2.2.1, hl.2.2.2⟩) measure_empty
    · rw [indicator_of_notMem hσ]
      exact measure_mono_null (fun l hl => hσ ⟨hl.2.1.1, hl.2.1.2⟩) measure_empty
  simp_rw [hin]
  exact lintegral_box _

/-- The two pieces meet in a null set (a subset of the line `x = 0`, `y = 1`). -/
lemma vol_Tex_XY (hs1 : s < 1) (hs0 : 0 < s) : volume ((Tex s ∩ Xt) ∩ (Tex s ∩ Yt)) = 0 := by
  have hk := kap_pos hs1 hs0
  apply measure_mono_null (t := {p : Fin 3 → ℝ | p 0 = 0})
  · rintro p ⟨hX, hY⟩
    rw [Tex_inter_Xt hs1 hs0] at hX
    rw [Tex_inter_Yt hs1 hs0] at hY
    obtain ⟨⟨h1, _⟩, ⟨_, hy1⟩, _⟩ := hX
    obtain ⟨_, ⟨hx0, _⟩, _⟩ := hY
    show p 0 = 0
    have : (p 1 - 1) * kap s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hk.le
    nlinarith
  · rw [volume_eq_iter orth_X 0 (isClosed_eq (continuous_apply 0) continuous_const).measurableSet]
    have : ∀ g σ : ℝ, volume {l : ℝ | framePsi 0 ex ey ez (g, σ, l) ∈ {p : Fin 3 → ℝ | p 0 = 0}} = 0 := by
      intro g σ
      simp only [framePsi_xyz, mem_ofPred_eq, Matrix.cons_val_zero]
      have hs : {l : ℝ | l = 0} = {0} := by ext; simp
      rw [hs, Real.volume_singleton]
    simp_rw [this, lintegral_zero]

/-- **Proposition 6.1.** -/
theorem relax : RelaxStatement := by
  intro s c hs0 hs1 hc
  refine ⟨fun ρ e f₁ f₂ h he => relax_upper hs0 hs1 h he, ?_⟩
  refine ⟨ρAx s, wAx s, nAx s, ez, orth_ex hs1 hs0, by simp [wAx, abs_of_pos hs0], ?_⟩
  have hk := kap_pos hs1 hs0
  have hksq := kap_sq hs1 hs0
  -- T ∩ (S_X ∪ S_Y(c)) = (T ∩ X) ∪ (T ∩ Y)
  have hset : tube (ρAx s) (wAx s) (nAx s) ez ∩ (SX ∪ SYc c) = (Tex s ∩ Xt) ∪ (Tex s ∩ Yt) := by
    ext p
    constructor
    · rintro ⟨hT, hp | hp⟩
      · exact Or.inl ⟨hT, SX_sub_Xt hp⟩
      · exact Or.inr ⟨hT, SYc_sub_Yt c hp⟩
    · rintro (⟨hT, hX⟩ | ⟨hT, hY⟩)
      · refine ⟨hT, Or.inl ?_⟩
        have hT' := (mem_Tex hs1 hs0 p).mp hT
        obtain ⟨hy0, hy1, hz0, hz1⟩ := hX
        have : (p 1 - 1) * kap s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hk.le
        refine ⟨?_, hy0, hy1, hz0, hz1⟩
        nlinarith [hT'.1.1]
      · refine ⟨hT, Or.inr ?_⟩
        have hT' := (mem_Tex hs1 hs0 p).mp hT
        obtain ⟨hx0, hx1, hz0, hz1⟩ := hY
        obtain ⟨⟨h1, h2⟩, _⟩ := hT'
        have hy1 : 1 ≤ p 1 := by
          by_contra hcon; push Not at hcon
          have : (p 1 - 1) * kap s < 0 := mul_neg_of_neg_of_pos (by linarith) hk
          nlinarith
        have hyc : p 1 ≤ 1 + (1 + s) / Real.sqrt (1 - s ^ 2) := by
          have hps : p 0 * s ≤ s := mul_le_of_le_one_left hs0.le hx1
          have : (p 1 - 1) * kap s ≤ 1 + s := by linarith
          have h3 : p 1 - 1 ≤ (1 + s) / kap s := by rw [le_div_iff₀ hk]; linarith
          have hkdef : kap s = Real.sqrt (1 - s ^ 2) := rfl
          rw [← hkdef]; linarith
        exact ⟨hx0, hx1, by linarith, hyc.trans hc, hz0, hz1⟩
  rw [hset]
  have hmeasY : MeasurableSet (Tex s ∩ Yt) := by
    rw [Tex_inter_Yt hs1 hs0]; exact measurableSet_halfspaces (by fun_prop) (by fun_prop) (by fun_prop)
  have hunion := measure_union_add_inter (Tex s ∩ Xt) hmeasY (μ := volume)
  rw [vol_Tex_XY hs1 hs0, add_zero, vol_Tex_X hs1 hs0, vol_Tex_Y hs1 hs0] at hunion
  rw [hunion, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rfl

end Extremal

end Sofa3D
