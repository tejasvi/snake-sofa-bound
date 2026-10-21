import Sofa3D.Defs

/-!
# Non-vacuity: the unit cube passes, so `V*(K_M) ≥ 1`

The cube `[-1, 0] × [0, 1] × [0, 1]` slides in the `x`-direction into the first corner and then in the
`y`-direction into the exit arm. The rotation stays the identity.
-/

open MeasureTheory Set

namespace Sofa3D

/-- The cube `[-1, 0] × [0, 1] × [0, 1]`. -/
def cube0 : Set (Fin 3 → ℝ) := {p | -1 ≤ p 0 ∧ p 0 ≤ 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 ∧ 0 ≤ p 2 ∧ p 2 ≤ 1}

lemma cube0_eq_pi : cube0 = Set.pi univ ![Icc (-1 : ℝ) 0, Icc 0 1, Icc 0 1] := by
  ext p
  simp only [cube0, mem_ofPred_eq, mem_pi, mem_univ, true_implies, Fin.forall_fin_succ]
  simp [mem_Icc, and_assoc]

lemma isBody_cube0 : IsBody cube0 := by
  rw [cube0_eq_pi]
  refine ⟨isCompact_univ_pi fun i => ?_, ?_⟩
  · fin_cases i <;> exact isCompact_Icc
  · refine (convex_pi fun i _ => ?_).isConnected ?_
    · fin_cases i <;> exact convex_Icc _ _
    · refine univ_pi_nonempty_iff.mpr fun i => ?_
      fin_cases i <;> simp

lemma volume_cube0 : volume cube0 = 1 := by
  rw [cube0_eq_pi, volume_pi_pi, Fin.prod_univ_three]
  simp [Real.volume_Icc]

/-- The motion of the cube: identity rotation, translation `(min (2t) 1, max 0 (2t − 1) (1 + M), 0)`. -/
noncomputable def cubePath (M : ℝ) (t : unitInterval) : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ) :=
  (1, ![min (2 * (t : ℝ)) 1, max 0 (2 * (t : ℝ) - 1) * (1 + M), 0])

lemma isPassage_cube (M : ℝ) (hM : 0 ≤ M) : IsPassage M cube0 (cubePath M) := by
  refine ⟨?_, fun _ => one_mem _, ?_, ?_, ?_⟩
  · refine continuous_const.prodMk (continuous_pi fun i => ?_)
    fin_cases i <;> simp <;> fun_prop
  · rintro t _ ⟨p, hp, rfl⟩
    obtain ⟨h0, h0', h1, h1', h2, h2'⟩ := hp
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    simp only [motion, cubePath, Matrix.one_mulVec]
    set a := min (2 * (t : ℝ)) 1 with ha
    set b := max 0 (2 * (t : ℝ) - 1) * (1 + M) with hb
    have ha0 : 0 ≤ a := le_min (by linarith) zero_le_one
    have ha1 : a ≤ 1 := min_le_right _ _
    have hb0 : 0 ≤ b := mul_nonneg (le_max_left _ _) (by linarith)
    have hb1 : b ≤ 1 + M := by
      have : max 0 (2 * (t : ℝ) - 1) ≤ 1 := max_le zero_le_one (by linarith)
      calc b ≤ 1 * (1 + M) := mul_le_mul_of_nonneg_right this (by linarith)
        _ = 1 + M := one_mul _
    have hab : a < 1 → b = 0 := by
      intro h
      have : 2 * (t : ℝ) < 1 := by
        by_contra hc; push Not at hc; rw [ha, min_eq_right hc] at h; exact lt_irrefl _ h
      rw [hb, max_eq_left (by linarith), zero_mul]
    simp only [corridor, SX, SY, SZ, mem_union, mem_ofPred_eq, Pi.add_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, add_zero]
    by_cases hq : p 0 + a < 0
    · have hb' : b = 0 := hab (by linarith)
      left; left
      refine ⟨by linarith, by linarith, by linarith, h2, h2'⟩
    · push Not at hq
      by_cases hq1 : p 1 + b ≤ 1 + M
      · left; right
        exact ⟨hq, by linarith, by linarith, hq1, h2, h2'⟩
      · right
        push Not at hq1
        exact ⟨hq, by linarith, by linarith, by linarith, h2⟩
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨h0, h0', h1, h1', h2, h2'⟩ := hp
    simp only [motion, cubePath, Matrix.one_mulVec, SX, mem_ofPred_eq, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Set.Icc.coe_zero, mul_zero, add_zero]
    norm_num
    exact ⟨h0', h1, h1', h2, h2'⟩
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨h0, h0', h1, h1', h2, h2'⟩ := hp
    simp only [motion, cubePath, Matrix.one_mulVec, SZ, mem_ofPred_eq, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Set.Icc.coe_one, mul_one, add_zero]
    norm_num
    exact ⟨by linarith, by linarith, by linarith, by linarith, h2⟩

/-- **Non-vacuity.** For every `M ≥ 0`, `V*(K_M) ≥ 1`. -/
theorem one_le_Vstar (M : ℝ) (hM : 0 ≤ M) : 1 ≤ Vstar M := by
  rw [← volume_cube0]
  exact le_iSup_of_le cube0 (le_iSup_of_le isBody_cube0 (le_iSup_of_le ⟨_, isPassage_cube M hM⟩ le_rfl))

end Sofa3D
