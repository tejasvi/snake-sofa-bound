import Sofa3D.Frame

/-!
# The tilt (Lemma 4.3, Tang's Lemma 5.1)

If a tube with axis direction `w` contains a point of `W₁` and a point of `W_{1+u}` (`u > √2`), then
`|w · e_y| ≥ (u² − 2)/(u² + 2)`.
-/

open MeasureTheory Set

namespace Sofa3D

/-- The window `W_c = [0, 1] × {c} × [0, 1]`. -/
def W (c : ℝ) : Set (Fin 3 → ℝ) := {p | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ p 1 = c ∧ 0 ≤ p 2 ∧ p 2 ≤ 1}

lemma dotProduct_fin3 (a b : Fin 3 → ℝ) : dotProduct a b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [dotProduct, Fin.sum_univ_three]

set_option maxHeartbeats 1000000 in
/-- **Lemma 4.3.** -/
theorem tilt {u : ℝ} (hu : Real.sqrt 2 < u) {ρ w f₁ f₂ p q : Fin 3 → ℝ} (h : Orthonormal3 w f₁ f₂)
    (hp : p ∈ tube ρ w f₁ f₂) (hq : q ∈ tube ρ w f₁ f₂) (hpW : p ∈ W 1) (hqW : q ∈ W (1 + u)) :
    (u ^ 2 - 2) / (u ^ 2 + 2) ≤ |w 1| := by
  rw [mem_tube_iff h] at hp hq
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  obtain ⟨px0, px1, py, pz0, pz1⟩ := hpW
  obtain ⟨qx0, qx1, qy, qz0, qz1⟩ := hqW
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 : 0 < u := hs2.trans hu
  have hu2 : 2 < u ^ 2 := by nlinarith
  set d := q - p with hd
  -- components of d along f₁, f₂ are at most 1 in absolute value
  have hd1 : |dotProduct d f₁| ≤ 1 := by
    have : dotProduct d f₁ = dotProduct (q - ρ) f₁ - dotProduct (p - ρ) f₁ := by
      rw [hd, ← sub_dotProduct]; congr 1; abel
    rw [this]
    calc |dotProduct (q - ρ) f₁ - dotProduct (p - ρ) f₁| ≤ |dotProduct (q - ρ) f₁| + |dotProduct (p - ρ) f₁| :=
          abs_sub _ _
      _ ≤ 1 / 2 + 1 / 2 := add_le_add hq1 hp1
      _ = 1 := by norm_num
  have hd2 : |dotProduct d f₂| ≤ 1 := by
    have : dotProduct d f₂ = dotProduct (q - ρ) f₂ - dotProduct (p - ρ) f₂ := by
      rw [hd, ← sub_dotProduct]; congr 1; abel
    rw [this]
    calc |dotProduct (q - ρ) f₂ - dotProduct (p - ρ) f₂| ≤ |dotProduct (q - ρ) f₂| + |dotProduct (p - ρ) f₂| :=
          abs_sub _ _
      _ ≤ 1 / 2 + 1 / 2 := add_le_add hq2 hp2
      _ = 1 := by norm_num
  -- |d|² − (d · w)² ≤ 2
  have hperp : dotProduct d d - dotProduct d w ^ 2 ≤ 2 := by
    have := h.dot_self d
    have e1 : dotProduct d f₁ ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr hd1
    have e2 : dotProduct d f₂ ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr hd2
    linarith
  -- coordinates
  set dx := d 0 with hdx
  set dz := d 2 with hdz
  have hdy : d 1 = u := by rw [hd, Pi.sub_apply, qy, py]; ring
  have hdx2 : dx ^ 2 ≤ 1 := by
    have h1 : dx = q 0 - p 0 := by rw [hdx, hd, Pi.sub_apply]
    rw [h1, sq_le_one_iff_abs_le_one, abs_le]; constructor <;> linarith
  have hdz2 : dz ^ 2 ≤ 1 := by
    have h1 : dz = q 2 - p 2 := by rw [hdz, hd, Pi.sub_apply]
    rw [h1, sq_le_one_iff_abs_le_one, abs_le]; constructor <;> linarith
  have hw : w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 = 1 := by
    have := h.1; rw [dotProduct_fin3] at this; linear_combination this
  set μ := |w 1| with hμ
  have hμ0 : 0 ≤ μ := abs_nonneg _
  have hμsq : μ ^ 2 = w 1 ^ 2 := sq_abs _
  set r := Real.sqrt (dx ^ 2 + dz ^ 2) with hr
  set ν := Real.sqrt (w 0 ^ 2 + w 2 ^ 2) with hν
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hν0 : 0 ≤ ν := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = dx ^ 2 + dz ^ 2 := Real.sq_sqrt (by positivity)
  have hνsq : ν ^ 2 = w 0 ^ 2 + w 2 ^ 2 := Real.sq_sqrt (by positivity)
  have hμν : μ ^ 2 + ν ^ 2 = 1 := by rw [hμsq, hνsq]; linarith
  -- |d · w| ≤ u μ + r ν
  have hA : |dx * w 0 + dz * w 2| ≤ r * ν := by
    have hcs : (dx * w 0 + dz * w 2) ^ 2 ≤ (r * ν) ^ 2 := by
      rw [mul_pow, hrsq, hνsq]
      have key : (dx ^ 2 + dz ^ 2) * (w 0 ^ 2 + w 2 ^ 2) - (dx * w 0 + dz * w 2) ^ 2 =
          (dx * w 2 - dz * w 0) ^ 2 := by ring
      linarith [sq_nonneg (dx * w 2 - dz * w 0)]
    exact abs_le_of_sq_le_sq' hcs (by positivity) |>.elim (fun h1 h2 => abs_le.mpr ⟨h1, h2⟩)
  have hdw : dotProduct d w = u * w 1 + (dx * w 0 + dz * w 2) := by
    rw [dotProduct_fin3, hdy]; ring
  have hdw_abs : |dotProduct d w| ≤ u * μ + r * ν := by
    rw [hdw]
    calc |u * w 1 + (dx * w 0 + dz * w 2)| ≤ |u * w 1| + |dx * w 0 + dz * w 2| := abs_add_le _ _
      _ ≤ u * μ + r * ν := by
        rw [abs_mul, abs_of_pos hu0]; linarith
  have hdd : dotProduct d d = u ^ 2 + r ^ 2 := by rw [dotProduct_fin3, hdy, hrsq]; ring
  -- (u ν − r μ)² ≤ 2
  have hsq : (u * ν - r * μ) ^ 2 ≤ 2 := by
    have h1 : dotProduct d w ^ 2 ≤ (u * μ + r * ν) ^ 2 := by
      have := sq_abs (dotProduct d w)
      nlinarith [abs_nonneg (dotProduct d w), hdw_abs]
    have h2 : (u * ν - r * μ) ^ 2 = u ^ 2 + r ^ 2 - (u * μ + r * ν) ^ 2 := by
      have : (u * ν - r * μ) ^ 2 - (u ^ 2 + r ^ 2 - (u * μ + r * ν) ^ 2) =
          u ^ 2 * (μ ^ 2 + ν ^ 2 - 1) + r ^ 2 * (μ ^ 2 + ν ^ 2 - 1) := by ring
      rw [hμν] at this; linarith
    rw [h2]; linarith
  -- u ν ≤ √2 (1 + μ)
  have hrle : r ≤ Real.sqrt 2 := by
    rw [hr]; exact Real.sqrt_le_sqrt (by linarith)
  have hstep : u * ν ≤ Real.sqrt 2 * (1 + μ) := by
    have h1 : u * ν - r * μ ≤ Real.sqrt 2 := by
      by_contra hc; push Not at hc
      have : Real.sqrt 2 ^ 2 < (u * ν - r * μ) ^ 2 := by nlinarith
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hrle hμ0]
  -- square and divide by 1 + μ
  have hsq2 : u ^ 2 * (1 - μ ^ 2) ≤ 2 * (1 + μ) ^ 2 := by
    have h1 : (u * ν) ^ 2 ≤ (Real.sqrt 2 * (1 + μ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hstep 2
    rw [mul_pow, mul_pow, hs2sq, hνsq] at h1
    have : w 0 ^ 2 + w 2 ^ 2 = 1 - μ ^ 2 := by rw [hμsq]; linarith
    rw [this] at h1; linarith
  have hfinal : u ^ 2 * (1 - μ) ≤ 2 * (1 + μ) := by
    have h1 : (1 + μ) * (u ^ 2 * (1 - μ) - 2 * (1 + μ)) ≤ 0 := by nlinarith
    have h2 : 0 < 1 + μ := by linarith
    nlinarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end Sofa3D
