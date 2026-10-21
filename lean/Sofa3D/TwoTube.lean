import Sofa3D.Frame
import Sofa3D.Chord

/-!
# Two tubes (Lemma 3.3): `vol(T ∩ T') ≤ 1/sin θ`

Frame: `e` (axis of `T`), `n` (unit normal of the plane of the two axes, built from the frame of `T'`), and
`m = (n · f₂) f₁ − (n · f₁) f₂`. In the coordinates `p = ρ + l e + s m + g n`:
* `p ∈ T` iff `s` lies in the chord of the square of `T` at height `g` (length `ℓ(g)`, independent of `l`);
* for fixed `(g, s)`, `{l | p ∈ T'}` has length `ℓ'(g + κ₀)/σ`, `σ = sin θ`, independent of `s`.
So `vol(T ∩ T') = (1/σ) ∫ ℓ(g) ℓ'(g + κ₀) dg ≤ (1/σ) (∫ ℓ² + ∫ ℓ'²)/2 ≤ 1/σ` by the chord lemma.
-/

open MeasureTheory Set

namespace Sofa3D

/-- `2ab ≤ a² + b²` in `ℝ≥0∞`. -/
lemma ENNReal.two_mul_le_sq_add_sq (a b : ENNReal) : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · rcases eq_or_ne b 0 with rfl | hb
    · simp
    · simp [ENNReal.top_pow, hb]
  rcases eq_or_ne b ⊤ with rfl | hb
  · rcases eq_or_ne a 0 with rfl | ha0
    · simp
    · simp [ENNReal.top_pow, ha0]
  lift a to NNReal using ha
  lift b to NNReal using hb
  have : (2 : NNReal) * (a * b) ≤ a ^ 2 + b ^ 2 := by
    have h := two_mul_le_add_sq (a : ℝ) b
    rw [← NNReal.coe_le_coe]; push_cast; linarith
  exact_mod_cast this

/-- Volume of an affine preimage in `ℝ`. -/
lemma volume_affine_preimage {a : ℝ} (ha : a ≠ 0) (b : ℝ) (A : Set ℝ) :
    volume ((fun l => a * l + b) ⁻¹' A) = ENNReal.ofReal |a⁻¹| * volume A := by
  have : (fun l => a * l + b) ⁻¹' A = (fun l => a * l) ⁻¹' ((fun x => x + b) ⁻¹' A) := rfl
  rw [this, Real.volume_preimage_mul_left ha, measure_preimage_add_right]

lemma measurable_chord (d₁ d₂ e₁ e₂ : ℝ) : Measurable (chord d₁ d₂ e₁ e₂) := by
  have hS : MeasurableSet {q : ℝ × ℝ | |q.2 * d₁ + q.1 * e₁| ≤ 1 / 2 ∧ |q.2 * d₂ + q.1 * e₂| ≤ 1 / 2} := by
    apply IsClosed.measurableSet
    apply IsClosed.inter
    · exact isClosed_le (f := fun q : ℝ × ℝ => |q.2 * d₁ + q.1 * e₁|) (by fun_prop) continuous_const
    · exact isClosed_le (f := fun q : ℝ × ℝ => |q.2 * d₂ + q.1 * e₂|) (by fun_prop) continuous_const
  exact measurable_measure_prodMk_left hS

set_option maxHeartbeats 1000000 in
/-- **Lemma 3.3 (the bound).** -/
theorem two_tube : TwoTubeStatement := by
  intro ρ e f₁ f₂ ρ' e' f₁' f₂' hT hT' hc
  obtain ⟨he, h11, h22, he1, he2, h12⟩ := hT
  obtain ⟨he', h11', h22', he1', he2', h12'⟩ := hT'
  have hTo : Orthonormal3 e f₁ f₂ := ⟨he, h11, h22, he1, he2, h12⟩
  have hTo' : Orthonormal3 e' f₁' f₂' := ⟨he', h11', h22', he1', he2', h12'⟩
  set c := dotProduct e e' with hc_def
  set α₁ := dotProduct e f₁' with hα₁
  set α₂ := dotProduct e f₂' with hα₂
  have hσ2 : α₁ ^ 2 + α₂ ^ 2 = 1 - c ^ 2 := by
    have := hTo'.dot_self e
    rw [he] at this; linarith
  have hc2 : c ^ 2 < 1 := by
    have : |c| ^ 2 < 1 := by nlinarith [abs_nonneg c]
    rwa [sq_abs] at this
  set σ := Real.sqrt (1 - c ^ 2) with hσ_def
  have hσ : 0 < σ := Real.sqrt_pos.mpr (by linarith)
  have hσsq : σ ^ 2 = α₁ ^ 2 + α₂ ^ 2 := by rw [hσ_def, Real.sq_sqrt (by linarith), hσ2]
  -- the unit normal `n` and `m`
  set a₁ := α₁ / σ with ha₁
  set a₂ := α₂ / σ with ha₂
  have ha : a₁ ^ 2 + a₂ ^ 2 = 1 := by
    rw [ha₁, ha₂, div_pow, div_pow, ← add_div, ← hσsq]; field_simp
  set n := (-a₂) • f₁' + a₁ • f₂' with hn
  have hne : dotProduct n e = 0 := by
    rw [hn, add_dotProduct, smul_dotProduct, smul_dotProduct, dotProduct_comm f₁' e,
      dotProduct_comm f₂' e, ← hα₁, ← hα₂, ha₁, ha₂]
    simp only [smul_eq_mul]; ring
  have hnn : dotProduct n n = 1 := by
    rw [hn]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul, h11', h22',
      h12', dotProduct_comm f₂' f₁']
    nlinarith [ha]
  set ν₁ := dotProduct n f₁ with hν₁
  set ν₂ := dotProduct n f₂ with hν₂
  have hν : ν₁ ^ 2 + ν₂ ^ 2 = 1 := by
    have := hTo.dot_self n
    rw [hnn, hne] at this; linarith
  set m := ν₂ • f₁ - ν₁ • f₂ with hm
  have hme : dotProduct m e = 0 := by
    rw [hm, sub_dotProduct, smul_dotProduct, smul_dotProduct, dotProduct_comm f₁ e,
      dotProduct_comm f₂ e, he1, he2]; simp
  have hmn : dotProduct m n = 0 := by
    rw [hm, sub_dotProduct, smul_dotProduct, smul_dotProduct, dotProduct_comm f₁ n,
      dotProduct_comm f₂ n, ← hν₁, ← hν₂]; simp only [smul_eq_mul]; ring
  have hmm : dotProduct m m = 1 := by
    rw [hm]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, h11, h22,
      h12, dotProduct_comm f₂ f₁]
    nlinarith [hν]
  have hmf₁ : dotProduct m f₁ = ν₂ := by
    rw [hm, sub_dotProduct, smul_dotProduct, smul_dotProduct, h11, dotProduct_comm f₂ f₁, h12]; simp
  have hmf₂ : dotProduct m f₂ = -ν₁ := by
    rw [hm, sub_dotProduct, smul_dotProduct, smul_dotProduct, h12, h22]; simp
  have hframe : Orthonormal3 e m n := by
    refine ⟨he, hmm, hnn, ?_, ?_, hmn⟩
    · rw [dotProduct_comm]; exact hme
    · rw [dotProduct_comm]; exact hne
  have hn' : dotProduct n e' = 0 := by
    rw [hn, add_dotProduct, smul_dotProduct, smul_dotProduct, dotProduct_comm f₁' e',
      dotProduct_comm f₂' e', he1', he2']; simp
  have hnf₁' : dotProduct n f₁' = -a₂ := by
    rw [hn, add_dotProduct, smul_dotProduct, smul_dotProduct, h11', dotProduct_comm f₂' f₁', h12']; simp
  have hnf₂' : dotProduct n f₂' = a₁ := by
    rw [hn, add_dotProduct, smul_dotProduct, smul_dotProduct, h12', h22']; simp
  -- Fubini in the frame (e, m, n) based at ρ
  have hmeas : MeasurableSet (tube ρ e f₁ f₂ ∩ tube ρ' e' f₁' f₂') :=
    (measurableSet_tube hTo).inter (measurableSet_tube hTo')
  rw [volume_eq_iter hframe ρ hmeas]
  set κ₀ := dotProduct (ρ - ρ') n with hκ₀
  -- the inner set, for fixed (g, s)
  have hinner : ∀ g s : ℝ, volume {l : ℝ | framePsi ρ e m n (g, s, l) ∈ tube ρ e f₁ f₂ ∩ tube ρ' e' f₁' f₂'} =
      {s' : ℝ | |s' * ν₂ + g * ν₁| ≤ 1 / 2 ∧ |s' * -ν₁ + g * ν₂| ≤ 1 / 2}.indicator
        (fun _ => ENNReal.ofReal σ⁻¹ * chord a₁ a₂ (-a₂) a₁ (g + κ₀)) s := by
    intro g s
    have hP : ∀ l : ℝ, framePsi ρ e m n (g, s, l) - ρ = l • e + s • m + g • n := by
      intro l; simp only [framePsi]; abel
    have hP' : ∀ l : ℝ, framePsi ρ e m n (g, s, l) - ρ' = (ρ - ρ') + l • e + s • m + g • n := by
      intro l; simp only [framePsi]; abel
    -- membership in T does not depend on l
    have hTmem : ∀ l : ℝ, framePsi ρ e m n (g, s, l) ∈ tube ρ e f₁ f₂ ↔
        (|s * ν₂ + g * ν₁| ≤ 1 / 2 ∧ |s * -ν₁ + g * ν₂| ≤ 1 / 2) := by
      intro l
      rw [mem_tube_iff hTo, hP l]
      simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, he1, he2, hmf₁, hmf₂, ← hν₁, ← hν₂,
        mul_zero, zero_add]
    -- membership in T' as an affine condition on l
    set β₁ := dotProduct (ρ - ρ' + s • m + g • n) f₁' with hβ₁
    set β₂ := dotProduct (ρ - ρ' + s • m + g • n) f₂' with hβ₂
    have hκ : -β₁ * a₂ + β₂ * a₁ = g + κ₀ := by
      have h1 : -β₁ * a₂ + β₂ * a₁ = dotProduct (ρ - ρ' + s • m + g • n) n := by
        rw [hβ₁, hβ₂, hTo'.dot_eq (ρ - ρ' + s • m + g • n) n, hn']
        rw [hnf₁', hnf₂']; ring
      rw [h1]
      simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, hmn, hnn, hκ₀]; ring
    have hT'mem : ∀ l : ℝ, framePsi ρ e m n (g, s, l) ∈ tube ρ' e' f₁' f₂' ↔
        (σ * l + (β₁ * a₁ + β₂ * a₂)) ∈
          {μ : ℝ | |μ * a₁ + (g + κ₀) * -a₂| ≤ 1 / 2 ∧ |μ * a₂ + (g + κ₀) * a₁| ≤ 1 / 2} := by
      intro l
      rw [mem_tube_iff hTo', hP' l, mem_ofPred_eq, ← hκ]
      have e1 : dotProduct (ρ - ρ' + l • e + s • m + g • n) f₁' = β₁ + l * α₁ := by
        rw [hβ₁, show ρ - ρ' + l • e + s • m + g • n = (ρ - ρ' + s • m + g • n) + l • e by abel,
          add_dotProduct, smul_dotProduct, smul_eq_mul]
      have e2 : dotProduct (ρ - ρ' + l • e + s • m + g • n) f₂' = β₂ + l * α₂ := by
        rw [hβ₂, show ρ - ρ' + l • e + s • m + g • n = (ρ - ρ' + s • m + g • n) + l • e by abel,
          add_dotProduct, smul_dotProduct, smul_eq_mul]
      rw [e1, e2]
      have hα₁' : α₁ = σ * a₁ := by rw [ha₁]; field_simp
      have hα₂' : α₂ = σ * a₂ := by rw [ha₂]; field_simp
      have k1 : β₁ + l * α₁ = (σ * l + (β₁ * a₁ + β₂ * a₂)) * a₁ + (-β₁ * a₂ + β₂ * a₁) * -a₂ := by
        rw [hα₁']; linear_combination (-β₁) * ha
      have k2 : β₂ + l * α₂ = (σ * l + (β₁ * a₁ + β₂ * a₂)) * a₂ + (-β₁ * a₂ + β₂ * a₁) * a₁ := by
        rw [hα₂']; linear_combination (-β₂) * ha
      rw [k1, k2]
    by_cases hs : |s * ν₂ + g * ν₁| ≤ 1 / 2 ∧ |s * -ν₁ + g * ν₂| ≤ 1 / 2
    · rw [indicator_of_mem (show s ∈ {s' : ℝ | |s' * ν₂ + g * ν₁| ≤ 1 / 2 ∧ |s' * -ν₁ + g * ν₂| ≤ 1 / 2}
        from hs)]
      have hset : {l : ℝ | framePsi ρ e m n (g, s, l) ∈ tube ρ e f₁ f₂ ∩ tube ρ' e' f₁' f₂'} =
          (fun l => σ * l + (β₁ * a₁ + β₂ * a₂)) ⁻¹'
            {μ : ℝ | |μ * a₁ + (g + κ₀) * -a₂| ≤ 1 / 2 ∧ |μ * a₂ + (g + κ₀) * a₁| ≤ 1 / 2} := by
        ext l
        simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
        rw [hTmem l, hT'mem l]
        simp only [hs, true_and, mem_ofPred_eq]
      rw [hset, volume_affine_preimage hσ.ne', abs_inv, abs_of_pos hσ]
      rfl
    · rw [indicator_of_notMem (show s ∉ {s' : ℝ | |s' * ν₂ + g * ν₁| ≤ 1 / 2 ∧ |s' * -ν₁ + g * ν₂| ≤ 1 / 2}
        from hs)]
      have hset : {l : ℝ | framePsi ρ e m n (g, s, l) ∈ tube ρ e f₁ f₂ ∩ tube ρ' e' f₁' f₂'} = ∅ := by
        ext l
        simp only [mem_ofPred_eq, mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
        intro h; exact absurd ((hTmem l).mp h) hs
      rw [hset, measure_empty]
  simp_rw [hinner]
  -- integrate in s
  have hchordset : ∀ g : ℝ, MeasurableSet
      {s' : ℝ | |s' * ν₂ + g * ν₁| ≤ 1 / 2 ∧ |s' * -ν₁ + g * ν₂| ≤ 1 / 2} := by
    intro g
    apply IsClosed.measurableSet
    apply IsClosed.inter
    · exact isClosed_le (f := fun s' : ℝ => |s' * ν₂ + g * ν₁|) (by fun_prop) continuous_const
    · exact isClosed_le (f := fun s' : ℝ => |s' * -ν₁ + g * ν₂|) (by fun_prop) continuous_const
  simp_rw [lintegral_indicator_const (hchordset _)]
  -- now: ∫ g, ofReal σ⁻¹ * chord' (g + κ₀) * chord_T g
  have hchordT : ∀ g, volume {s' : ℝ | |s' * ν₂ + g * ν₁| ≤ 1 / 2 ∧ |s' * -ν₁ + g * ν₂| ≤ 1 / 2} =
      chord ν₂ (-ν₁) ν₁ ν₂ g := fun g => rfl
  simp_rw [hchordT]
  have hσ' : 1 / Real.sqrt (1 - c ^ 2) = σ⁻¹ := by rw [one_div]
  rw [hσ']
  calc ∫⁻ g, ENNReal.ofReal σ⁻¹ * chord a₁ a₂ (-a₂) a₁ (g + κ₀) * chord ν₂ (-ν₁) ν₁ ν₂ g
      = ENNReal.ofReal σ⁻¹ * ∫⁻ g, chord a₁ a₂ (-a₂) a₁ (g + κ₀) * chord ν₂ (-ν₁) ν₁ ν₂ g := by
        simp_rw [mul_assoc]
        exact lintegral_const_mul _ (((measurable_chord _ _ _ _).comp (measurable_add_const κ₀)).mul
          (measurable_chord _ _ _ _))
    _ ≤ ENNReal.ofReal σ⁻¹ * 1 := by
        gcongr
        set F := fun g => chord a₁ a₂ (-a₂) a₁ (g + κ₀) with hF
        set G := fun g => chord ν₂ (-ν₁) ν₁ ν₂ g with hG
        have hFm : Measurable F := (measurable_chord _ _ _ _).comp (measurable_add_const κ₀)
        have hGm : Measurable G := measurable_chord _ _ _ _
        have hF2 : ∫⁻ g, F g ^ 2 ≤ 1 := by
          have := lintegral_add_right_eq_self (μ := volume) (fun g => chord a₁ a₂ (-a₂) a₁ g ^ 2) κ₀
          show ∫⁻ g, chord a₁ a₂ (-a₂) a₁ (g + κ₀) ^ 2 ≤ 1
          rw [this]
          exact chord_sq_le_one ha (by nlinarith [ha]) (by ring)
        have hG2 : ∫⁻ g, G g ^ 2 ≤ 1 := chord_sq_le_one (by nlinarith [hν]) hν (by ring)
        have h2 : 2 * ∫⁻ g, F g * G g ≤ 2 * 1 := by
          calc 2 * ∫⁻ g, F g * G g = ∫⁻ g, 2 * (F g * G g) := (lintegral_const_mul 2 (hFm.mul hGm)).symm
            _ ≤ ∫⁻ g, (F g ^ 2 + G g ^ 2) := lintegral_mono fun g => ENNReal.two_mul_le_sq_add_sq _ _
            _ = (∫⁻ g, F g ^ 2) + ∫⁻ g, G g ^ 2 := lintegral_add_left (hFm.pow_const 2) _
            _ ≤ 1 + 1 := add_le_add hF2 hG2
            _ = 2 * 1 := by norm_num
        exact (ENNReal.mul_le_mul_iff_right (a := 2) (by simp) (by simp)).1 h2
    _ = ENNReal.ofReal σ⁻¹ := mul_one _

end Sofa3D
