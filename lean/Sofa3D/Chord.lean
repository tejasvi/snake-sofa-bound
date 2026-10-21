import Mathlib

/-!
# The chord lemma (Lemma 3.2)

For an orthonormal pair `(d, e)` of vectors of `ℝ²`, the chord function of the square `Q₀ = [-1/2, 1/2]²` is
`ℓ(g) = length {μ | μ d + g e ∈ Q₀}`. We prove `∫ ℓ(g)² dg ≤ 1`.

The chord `{μ | μ d + g e ∈ Q₀}` is the intersection of two intervals of lengths `1/|d₁|` and `1/|d₂|` whose
centres are `|g|/(|d₁| |d₂|)` apart, so `ℓ` is an explicit trapezoid, and `∫ ℓ² = 1/a − b/(3a²)` with
`a = max(|d₁|, |d₂|)`, `b = min(|d₁|, |d₂|)`.
-/

open MeasureTheory Set

namespace Sofa3D

/-- The chord function of `Q₀ = [-1/2, 1/2]²` for vectors `d = (d₁, d₂)`, `e = (e₁, e₂)`:
the length of `{μ | μ d + g e ∈ Q₀}`. -/
noncomputable def chord (d₁ d₂ e₁ e₂ g : ℝ) : ENNReal :=
  volume {μ : ℝ | |μ * d₁ + g * e₁| ≤ 1 / 2 ∧ |μ * d₂ + g * e₂| ≤ 1 / 2}

lemma abs_mul_add_le_half_iff {d c μ : ℝ} (hd : d ≠ 0) :
    |μ * d + c| ≤ 1 / 2 ↔ μ ∈ Icc (-c / d - 1 / (2 * |d|)) (-c / d + 1 / (2 * |d|)) := by
  have hpos : 0 < |d| := abs_pos.mpr hd
  have key : μ * d + c = d * (μ - (-c / d)) := by field_simp; ring
  rw [key, abs_mul, mem_Icc]
  constructor
  · intro h
    have h' : |μ - -c / d| ≤ 1 / (2 * |d|) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [abs_nonneg (μ - -c / d)]
    constructor <;> linarith [abs_le.mp h']
  · rintro ⟨h1, h2⟩
    have h' : |μ - -c / d| ≤ 1 / (2 * |d|) := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [le_div_iff₀ (by positivity)] at h'
    nlinarith [abs_nonneg (μ - -c / d)]

/-- `min (b₁, b₂) - max (a₁, a₂)` for two centred intervals. -/
lemma min_sub_max_centred (c₁ c₂ r₁ r₂ : ℝ) :
    min (c₁ + r₁) (c₂ + r₂) - max (c₁ - r₁) (c₂ - r₂) =
      min (min (2 * r₁) (2 * r₂)) (r₁ + r₂ - |c₁ - c₂|) := by
  rcases abs_cases (c₁ - c₂) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
  · simp only [min_def, max_def]
    split_ifs <;> linarith

/-- The chord as an explicit length, for `d₁ ≠ 0`, `d₂ ≠ 0`. -/
lemma chord_eq (d₁ d₂ e₁ e₂ g : ℝ) (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) :
    chord d₁ d₂ e₁ e₂ g = ENNReal.ofReal
      (min (min (1 / |d₁|) (1 / |d₂|))
        (1 / (2 * |d₁|) + 1 / (2 * |d₂|) - |-(g * e₁) / d₁ - -(g * e₂) / d₂|)) := by
  unfold chord
  have hs : {μ : ℝ | |μ * d₁ + g * e₁| ≤ 1 / 2 ∧ |μ * d₂ + g * e₂| ≤ 1 / 2} =
      Icc (-(g * e₁) / d₁ - 1 / (2 * |d₁|)) (-(g * e₁) / d₁ + 1 / (2 * |d₁|)) ∩
      Icc (-(g * e₂) / d₂ - 1 / (2 * |d₂|)) (-(g * e₂) / d₂ + 1 / (2 * |d₂|)) := by
    ext μ
    simp only [mem_ofPred_eq, mem_inter_iff, abs_mul_add_le_half_iff h₁, abs_mul_add_le_half_iff h₂]
  rw [hs, Icc_inter_Icc, Real.volume_Icc]
  congr 1
  have := min_sub_max_centred (-(g * e₁) / d₁) (-(g * e₂) / d₂) (1 / (2 * |d₁|)) (1 / (2 * |d₂|))
  have e1 : 2 * (1 / (2 * |d₁|)) = 1 / |d₁| := by field_simp
  have e2 : 2 * (1 / (2 * |d₂|)) = 1 / |d₂| := by field_simp
  rw [e1, e2] at this
  simpa using this

/-- The trapezoid `ψ(g) = max(min(min(1/a, 1/b), ((a + b)/2 − |g|)/(ab)), 0)`. -/
noncomputable def trap (a b g : ℝ) : ℝ := max (min (min (1 / a) (1 / b)) (((a + b) / 2 - |g|) / (a * b))) 0

lemma chord_eq_trap {d₁ d₂ e₁ e₂ : ℝ} (hd : d₁ ^ 2 + d₂ ^ 2 = 1) (he : e₁ ^ 2 + e₂ ^ 2 = 1)
    (hde : d₁ * e₁ + d₂ * e₂ = 0) (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) (g : ℝ) :
    chord d₁ d₂ e₁ e₂ g = ENNReal.ofReal (trap |d₁| |d₂| g) := by
  rw [chord_eq d₁ d₂ e₁ e₂ g h₁ h₂, trap, ENNReal.ofReal_max, ENNReal.ofReal_zero, max_zero]
  congr 2
  have hdet : |e₂ * d₁ - e₁ * d₂| = 1 := by
    have hsq : (e₂ * d₁ - e₁ * d₂) ^ 2 = 1 := by nlinarith [hd, he, hde]
    have := abs_mul_abs_self (e₂ * d₁ - e₁ * d₂)
    nlinarith [abs_nonneg (e₂ * d₁ - e₁ * d₂), sq_abs (e₂ * d₁ - e₁ * d₂)]
  have hc : -(g * e₁) / d₁ - -(g * e₂) / d₂ = g * (e₂ * d₁ - e₁ * d₂) / (d₁ * d₂) := by
    field_simp; ring
  have ha : 0 < |d₁| := abs_pos.mpr h₁
  have hb : 0 < |d₂| := abs_pos.mpr h₂
  rw [hc, abs_div, abs_mul, abs_mul, hdet, mul_one]
  field_simp
  ring

lemma trap_comm (a b g : ℝ) : trap a b g = trap b a g := by
  simp only [trap, min_comm (1 / a) (1 / b), add_comm a b, mul_comm a b]

lemma trap_nonneg (a b g : ℝ) : 0 ≤ trap a b g := le_max_right _ _

lemma continuous_trap (a b : ℝ) : Continuous (trap a b) := by
  unfold trap; fun_prop

lemma trap_eq_zero {a b g : ℝ} (ha : 0 < a) (hb : 0 < b) (hg : (a + b) / 2 ≤ |g|) : trap a b g = 0 := by
  unfold trap
  apply max_eq_right
  apply (min_le_right _ _).trans
  apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

/-- `∫ ψ² = 1/a − b/(3a²)` for `0 < b ≤ a`. -/
lemma integral_trap_sq {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) :
    ∫ g, trap a b g ^ 2 = 1 / a - b / (3 * a ^ 2) := by
  have ha : 0 < a := hb.trans_le hba
  set W := (a + b) / 2 with hW
  set V := (a - b) / 2 with hV
  have hVW : V ≤ W := by rw [hV, hW]; linarith
  have hV0 : 0 ≤ V := by rw [hV]; linarith
  have hmin : min (1 / a) (1 / b) = 1 / a := min_eq_left (one_div_le_one_div_of_le hb hba)
  -- the integral over ℝ is the integral over [-W, W]
  have hsupp : ∀ g, g ∉ Icc (-W) W → trap a b g ^ 2 = 0 := by
    intro g hg
    have : W ≤ |g| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hg
      rcases hg with hg | hg
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [trap_eq_zero ha hb this]; ring
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  -- pieces
  have hcont : Continuous fun g => trap a b g ^ 2 := (continuous_trap a b).pow 2
  have hint : ∀ x y : ℝ, IntervalIntegrable (fun g => trap a b g ^ 2) volume x y :=
    fun x y => hcont.intervalIntegrable x y
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-W) (-V)) (hint (-V) W),
    ← intervalIntegral.integral_add_adjacent_intervals (hint (-V) V) (hint V W)]
  -- middle: ψ = 1/a
  have hmid : ∫ g in (-V)..V, trap a b g ^ 2 = (2 * V) * (1 / a) ^ 2 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 / a) ^ 2)]
    · rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    · intro g hg
      rw [uIcc_of_le (by linarith), mem_Icc] at hg
      have hg' : |g| ≤ V := abs_le.mpr ⟨hg.1, hg.2⟩
      simp only [trap, hmin]
      have : 1 / a ≤ (W - |g|) / (a * b) := by
        rw [div_le_div_iff₀ ha (by positivity)]; rw [hW] at *; rw [hV] at hg'; nlinarith
      rw [min_eq_left this, max_eq_left (by positivity)]
  -- right ramp: ψ = (W - g)/(ab)
  have hright : ∫ g in V..W, trap a b g ^ 2 = b / (3 * a ^ 2) := by
    rw [intervalIntegral.integral_congr (g := fun g => ((W - g) / (a * b)) ^ 2)]
    · have hderiv : ∀ x ∈ uIcc V W, HasDerivAt (fun g => -(W - g) ^ 3 / (3 * (a * b) ^ 2))
          (((W - x) / (a * b)) ^ 2) x := by
        intro x _
        have h1 : HasDerivAt (fun g => W - g) (-1) x := by
          simpa using (hasDerivAt_id x).const_sub W
        have h2 := (h1.pow 3).neg.div_const (3 * (a * b) ^ 2)
        convert h2 using 1
        field_simp
        ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        ((by fun_prop : Continuous fun g => ((W - g) / (a * b)) ^ 2).intervalIntegrable V W)]
      have : W - V = b := by rw [hW, hV]; ring
      simp only [sub_self, this]
      field_simp
      ring
    · intro g hg
      rw [uIcc_of_le hVW, mem_Icc] at hg
      have hg0 : 0 ≤ g := hV0.trans hg.1
      simp only [trap, hmin, abs_of_nonneg hg0]
      have h1 : (W - g) / (a * b) ≤ 1 / a := by
        rw [div_le_div_iff₀ (by positivity) ha]; rw [hW] at *; rw [hV] at hg; nlinarith
      rw [min_eq_right h1, max_eq_left (div_nonneg (by linarith) (by positivity))]
  -- left ramp, by the symmetry g ↦ -g
  have hleft : ∫ g in (-W)..(-V), trap a b g ^ 2 = b / (3 * a ^ 2) := by
    have hsym : ∀ g, trap a b (-g) ^ 2 = trap a b g ^ 2 := by intro g; simp [trap, abs_neg]
    rw [← hright, ← intervalIntegral.integral_comp_neg]
    simp only [hsym]
  rw [hleft, hmid, hright, hV]
  field_simp
  ring

/-- The final inequality `1/a − b/(3a²) ≤ 1` for `a² + b² = 1`, `0 < b ≤ a`. -/
lemma trap_bound {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) (hab : a ^ 2 + b ^ 2 = 1) :
    1 / a - b / (3 * a ^ 2) ≤ 1 := by
  have ha : 0 < a := hb.trans_le hba
  have h2ab : 2 * (a * b) ≤ 1 := by nlinarith [sq_nonneg (a - b)]
  have ha2 : 1 ≤ 2 * a ^ 2 := by nlinarith
  have ha' : 1 / 2 < a := by nlinarith
  have key : 3 * a * (1 - a) ≤ b := by
    have h1 : (1 - a) * (1 + a) = b ^ 2 := by nlinarith
    have h3 : 3 * a * b ≤ 1 + a := by nlinarith
    nlinarith [mul_pos ha hb]
  rw [div_sub_div _ _ (ne_of_gt ha) (by positivity), div_le_one (by positivity)]
  nlinarith

/-- Degenerate case: `d = (0, ±1)`. -/
lemma chord_axis {d₂ e₁ : ℝ} (hd : |d₂| = 1) (he : |e₁| = 1) (g : ℝ) :
    chord 0 d₂ e₁ 0 g = (Icc (-1 / 2 : ℝ) (1 / 2)).indicator 1 g := by
  unfold chord
  simp only [mul_zero, zero_add, add_zero, abs_mul, he, mul_one, hd]
  by_cases hg : |g| ≤ 1 / 2
  · have : g ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
      rw [mem_Icc]; constructor <;> linarith [abs_le.mp hg]
    rw [indicator_of_mem this]
    simp only [hg, true_and, Pi.one_apply]
    have hs : {μ : ℝ | |μ| ≤ 1 / 2} = Icc (-1 / 2) (1 / 2) := by
      ext μ; simp only [mem_ofPred_eq, mem_Icc, abs_le]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [hs, Real.volume_Icc]; norm_num
  · have : g ∉ Icc (-1 / 2 : ℝ) (1 / 2) := by
      rw [mem_Icc]; intro h; exact hg (abs_le.mpr ⟨by linarith [h.1], h.2⟩)
    rw [indicator_of_notMem this]
    exact measure_mono_null (fun μ hμ => absurd hμ.1 hg) measure_empty

lemma lintegral_indicator_sq_Icc :
    ∫⁻ g, ((Icc (-1 / 2 : ℝ) (1 / 2)).indicator (1 : ℝ → ENNReal) g) ^ 2 = 1 := by
  have : ∀ g, ((Icc (-1 / 2 : ℝ) (1 / 2)).indicator (1 : ℝ → ENNReal) g) ^ 2 =
      (Icc (-1 / 2 : ℝ) (1 / 2)).indicator 1 g := by
    intro g
    by_cases h : g ∈ Icc (-1 / 2 : ℝ) (1 / 2)
    · rw [indicator_of_mem h, Pi.one_apply, one_pow]
    · rw [indicator_of_notMem h]; simp
  simp_rw [this]
  rw [lintegral_indicator_one measurableSet_Icc, Real.volume_Icc]; norm_num

lemma chord_swap (d₁ d₂ e₁ e₂ g : ℝ) : chord d₁ d₂ e₁ e₂ g = chord d₂ d₁ e₂ e₁ g := by
  unfold chord; congr 1; ext μ; simp only [mem_ofPred_eq]; exact and_comm

lemma abs_eq_one_of_sq {x : ℝ} (h : x ^ 2 = 1) : |x| = 1 := by
  have h2 : |x| ^ 2 = 1 := by rw [sq_abs]; exact h
  exact le_antisymm (by nlinarith [abs_nonneg x]) (by nlinarith [abs_nonneg x])

/-- The case `d₁ = 0`. -/
lemma chord_sq_le_one_axis {d₂ e₁ e₂ : ℝ} (hd : (0 : ℝ) ^ 2 + d₂ ^ 2 = 1) (he : e₁ ^ 2 + e₂ ^ 2 = 1)
    (hde : 0 * e₁ + d₂ * e₂ = 0) : ∫⁻ g, chord 0 d₂ e₁ e₂ g ^ 2 ≤ 1 := by
  have hd2 : |d₂| = 1 := abs_eq_one_of_sq (by linarith)
  have hd2' : d₂ ≠ 0 := by intro h; rw [h, abs_zero] at hd2; exact zero_ne_one hd2
  have he2 : e₂ = 0 := by
    have : d₂ * e₂ = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hd2'
    · exact h
  subst he2
  have he1 : |e₁| = 1 := abs_eq_one_of_sq (by linarith)
  simp_rw [chord_axis hd2 he1]
  rw [lintegral_indicator_sq_Icc]

/-- **Lemma 3.2 (the bound).** For an orthonormal pair `(d, e)` of `ℝ²`, `∫ ℓ(g)² dg ≤ 1`. -/
theorem chord_sq_le_one {d₁ d₂ e₁ e₂ : ℝ} (hd : d₁ ^ 2 + d₂ ^ 2 = 1) (he : e₁ ^ 2 + e₂ ^ 2 = 1)
    (hde : d₁ * e₁ + d₂ * e₂ = 0) : ∫⁻ g, chord d₁ d₂ e₁ e₂ g ^ 2 ≤ 1 := by
  by_cases h₁ : d₁ = 0
  · subst h₁; exact chord_sq_le_one_axis hd he hde
  by_cases h₂ : d₂ = 0
  · subst h₂
    simp_rw [chord_swap d₁ 0 e₁ e₂]
    exact chord_sq_le_one_axis (by linarith) (by linarith) (by linarith)
  simp_rw [chord_eq_trap hd he hde h₁ h₂]
  have hpow : ∀ g, ENNReal.ofReal (trap |d₁| |d₂| g) ^ 2 = ENNReal.ofReal (trap |d₁| |d₂| g ^ 2) :=
    fun g => (ENNReal.ofReal_pow (trap_nonneg _ _ _) 2).symm
  simp_rw [hpow]
  have ha : 0 < |d₁| := abs_pos.mpr h₁
  have hb : 0 < |d₂| := abs_pos.mpr h₂
  have hab : |d₁| ^ 2 + |d₂| ^ 2 = 1 := by rw [sq_abs, sq_abs]; exact hd
  have hcs : HasCompactSupport (fun g => trap |d₁| |d₂| g ^ 2) := by
    apply HasCompactSupport.intro (isCompact_Icc (a := -((|d₁| + |d₂|) / 2)) (b := (|d₁| + |d₂|) / 2))
    intro g hg
    have : (|d₁| + |d₂|) / 2 ≤ |g| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hg
      rcases hg with hg | hg
      · rw [abs_of_neg (show g < 0 by linarith)]; linarith
      · rw [abs_of_pos (show 0 < g by linarith)]; linarith
    simp only [trap_eq_zero ha hb this]; ring
  have hint : Integrable (fun g => trap |d₁| |d₂| g ^ 2) :=
    ((continuous_trap _ _).pow 2).integrable_of_hasCompactSupport hcs
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun g => sq_nonneg _)]
  apply ENNReal.ofReal_le_one.mpr
  rcases le_total |d₂| |d₁| with h | h
  · rw [integral_trap_sq hb h]; exact trap_bound hb h hab
  · simp_rw [trap_comm |d₁| |d₂|]
    rw [integral_trap_sq ha h]; exact trap_bound ha h (by linarith)

end Sofa3D
