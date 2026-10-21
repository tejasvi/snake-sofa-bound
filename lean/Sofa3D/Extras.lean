import Sofa3D.Main

/-!
# Proposition 6.1's last sentence; bounded connected sets (Remark 2.3)
-/

open MeasureTheory Set

namespace Sofa3D

/-- **Proposition 6.1, last sentence.** -/
theorem relax_value : RelaxValueStatement := by
  intro s hs0 hs1
  set c := Real.sqrt (1 - s ^ 2) with hc
  have h1s : 0 < 1 - s ^ 2 := by nlinarith
  have hc0 : 0 < c := Real.sqrt_pos.mpr h1s
  have hcsq : c ^ 2 = 1 - s ^ 2 := Real.sq_sqrt h1s.le
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hx0 : 0 < s * c := mul_pos hs0 hc0
  have hx : s * c ≤ 1 / 2 := by nlinarith [sq_nonneg (s - c)]
  have hsc2 : (s + c) ^ 2 = 1 + 2 * (s * c) := by nlinarith
  have h8 : (2 * Real.sqrt 2 * (s * c)) ^ 2 = 8 * (s * c) ^ 2 := by
    rw [mul_pow, mul_pow, h2]; ring
  have key : 2 * Real.sqrt 2 * (s * c) ≤ s + c := by
    have hsq : (2 * Real.sqrt 2 * (s * c)) ^ 2 ≤ (s + c) ^ 2 := by
      rw [h8, hsc2]; nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  have hval : 1 / s + 1 / c = (s + c) / (s * c) := by field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hval, le_div_iff₀ hx0]; linarith
  · intro heq
    rw [hval, div_eq_iff hx0.ne'] at heq
    -- (s + c)² = 8 (sc)², so sc = 1/2, so s = c
    have hsq : 1 + 2 * (s * c) = 8 * (s * c) ^ 2 := by rw [← hsc2, heq, ← h8]
    have hx2 : s * c = 1 / 2 := by
      have : (4 * (s * c) + 1) * (2 * (s * c) - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · nlinarith
      · linarith
    have hsc : s = c := by nlinarith [sq_nonneg (s - c)]
    have hs2' : s ^ 2 = 1 / 2 := by rw [← hsc] at hcsq; linarith
    have : s * Real.sqrt 2 = 1 := by
      have h' : (s * Real.sqrt 2) ^ 2 = 1 := by rw [mul_pow, hs2', h2]; norm_num
      nlinarith [mul_pos hs0 hs2]
    field_simp; linarith
  · rintro rfl
    exact bound_at_half

lemma isClosed_SX : IsClosed SX := by
  simp only [SX, Set.setOf_and]
  exact (isClosed_le (continuous_apply 0) continuous_const).inter
    ((isClosed_le continuous_const (continuous_apply 1)).inter
    ((isClosed_le (continuous_apply 1) continuous_const).inter
    ((isClosed_le continuous_const (continuous_apply 2)).inter
    (isClosed_le (continuous_apply 2) continuous_const))))

lemma isClosed_SY (M : ℝ) : IsClosed (SY M) := by
  simp only [SY, Set.setOf_and]
  exact (isClosed_le continuous_const (continuous_apply 0)).inter
    ((isClosed_le (continuous_apply 0) continuous_const).inter
    ((isClosed_le continuous_const (continuous_apply 1)).inter
    ((isClosed_le (continuous_apply 1) continuous_const).inter
    ((isClosed_le continuous_const (continuous_apply 2)).inter
    (isClosed_le (continuous_apply 2) continuous_const)))))

lemma isClosed_SZ (M : ℝ) : IsClosed (SZ M) := by
  simp only [SZ, Set.setOf_and]
  exact (isClosed_le continuous_const (continuous_apply 0)).inter
    ((isClosed_le (continuous_apply 0) continuous_const).inter
    ((isClosed_le continuous_const (continuous_apply 1)).inter
    ((isClosed_le (continuous_apply 1) continuous_const).inter
    (isClosed_le continuous_const (continuous_apply 2)))))

lemma isClosed_corridor (M : ℝ) : IsClosed (corridor M) :=
  ((isClosed_SX).union (isClosed_SY M)).union (isClosed_SZ M)

/-- **Remark 2.3, bounded connected sets.** -/
theorem bounded : BoundedStatement := by
  intro M hM E g hEb hEc hg
  have hcl : IsBody (closure E) :=
    ⟨Metric.isCompact_of_isClosed_isBounded isClosed_closure hEb.closure, hEc.closure⟩
  have hcont : ∀ t, Continuous (motion (g t)) := fun t =>
    continuous_motion_joint.comp (continuous_const.prodMk continuous_id)
  have hsub : ∀ t (C : Set (Fin 3 → ℝ)), IsClosed C → motion (g t) '' E ⊆ C → motion (g t) '' closure E ⊆ C :=
    fun t C hC h => (image_closure_subset_closure_image (hcont t)).trans (closure_minimal h hC)
  have hgc : IsPassage M (closure E) g :=
    ⟨hg.continuous, hg.rotation, fun t => hsub t _ (isClosed_corridor M) (hg.inside t),
      hsub 0 _ isClosed_SX hg.start, hsub 1 _ (isClosed_SZ M) hg.finish⟩
  exact (measure_mono subset_closure).trans (weak M hM _ g hcl (hgc.weak hcl))

end Sofa3D
