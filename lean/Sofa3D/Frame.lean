import Sofa3D.Statements

/-!
# Orthonormal frames of `ℝ³`

For an orthonormal triple `(v₀, v₁, v₂)`: the expansion `p = Σ (p · vᵢ) vᵢ`, the coordinate description of tubes,
and Fubini in the frame: the map `(g, s, l) ↦ ρ + l v₀ + s v₁ + g v₂` is measure preserving, so
`vol S = ∫ g, ∫ s, length {l | ρ + l v₀ + s v₁ + g v₂ ∈ S}`.
-/

open MeasureTheory Set

namespace Sofa3D

section Orthonormal

variable {v₀ v₁ v₂ : Fin 3 → ℝ}

lemma Orthonormal3.symm_dots (h : Orthonormal3 v₀ v₁ v₂) :
    dotProduct v₁ v₀ = 0 ∧ dotProduct v₂ v₀ = 0 ∧ dotProduct v₂ v₁ = 0 := by
  obtain ⟨_, _, _, h01, h02, h12⟩ := h
  exact ⟨by rw [dotProduct_comm]; exact h01, by rw [dotProduct_comm]; exact h02,
    by rw [dotProduct_comm]; exact h12⟩

/-- The rows `v₀, v₁, v₂` as a matrix. -/
def rowsMat (v₀ v₁ v₂ : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![v₀, v₁, v₂]

lemma Orthonormal3.mul_transpose (h : Orthonormal3 v₀ v₁ v₂) :
    rowsMat v₀ v₁ v₂ * (rowsMat v₀ v₁ v₂).transpose = 1 := by
  obtain ⟨s1, s2, s3⟩ := h.symm_dots
  obtain ⟨h00, h11, h22, h01, h02, h12⟩ := h
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [rowsMat, Matrix.one_apply, dotProduct] at * <;> simp [h00, h11, h22, h01, h02, h12, s1, s2, s3]

lemma Orthonormal3.transpose_mul (h : Orthonormal3 v₀ v₁ v₂) :
    (rowsMat v₀ v₁ v₂).transpose * rowsMat v₀ v₁ v₂ = 1 :=
  mul_eq_one_comm.mp h.mul_transpose

lemma Orthonormal3.sum_sq (h : Orthonormal3 v₀ v₁ v₂) (j k : Fin 3) :
    v₀ j * v₀ k + v₁ j * v₁ k + v₂ j * v₂ k = if j = k then 1 else 0 := by
  have := congrFun (congrFun h.transpose_mul j) k
  simpa [rowsMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] using this

/-- The expansion of a vector in an orthonormal frame. -/
lemma Orthonormal3.expand (h : Orthonormal3 v₀ v₁ v₂) (p : Fin 3 → ℝ) :
    p = dotProduct p v₀ • v₀ + dotProduct p v₁ • v₁ + dotProduct p v₂ • v₂ := by
  funext j
  have e : p j = ∑ k, (if j = k then 1 else 0) * p k := by simp
  rw [e]
  simp_rw [← h.sum_sq j]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Fin.sum_univ_three]
  ring

/-- `(p · q) = Σ (p · vᵢ)(q · vᵢ)`. -/
lemma Orthonormal3.dot_eq (h : Orthonormal3 v₀ v₁ v₂) (p q : Fin 3 → ℝ) :
    dotProduct p q = dotProduct p v₀ * dotProduct q v₀ + dotProduct p v₁ * dotProduct q v₁ +
      dotProduct p v₂ * dotProduct q v₂ := by
  have e := h.expand p
  calc dotProduct p q
      = dotProduct (dotProduct p v₀ • v₀ + dotProduct p v₁ • v₁ + dotProduct p v₂ • v₂) q := by
        rw [← e]
    _ = _ := by
        simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
        rw [dotProduct_comm v₀ q, dotProduct_comm v₁ q, dotProduct_comm v₂ q]

/-- `|p|² = Σ (p · vᵢ)²`. -/
lemma Orthonormal3.dot_self (h : Orthonormal3 v₀ v₁ v₂) (p : Fin 3 → ℝ) :
    dotProduct p p = dotProduct p v₀ ^ 2 + dotProduct p v₁ ^ 2 + dotProduct p v₂ ^ 2 := by
  rw [h.dot_eq p p]; ring

end Orthonormal

/-- Tubes in coordinates. -/
lemma mem_tube_iff {ρ e f₁ f₂ : Fin 3 → ℝ} (h : Orthonormal3 e f₁ f₂) (p : Fin 3 → ℝ) :
    p ∈ tube ρ e f₁ f₂ ↔ |dotProduct (p - ρ) f₁| ≤ 1 / 2 ∧ |dotProduct (p - ρ) f₂| ≤ 1 / 2 := by
  obtain ⟨h00, h11, h22, h01, h02, h12⟩ := h
  have s := Orthonormal3.symm_dots ⟨h00, h11, h22, h01, h02, h12⟩
  constructor
  · rintro ⟨l, a, b, ha, hb, rfl⟩
    have e1 : dotProduct (ρ + l • e + a • f₁ + b • f₂ - ρ) f₁ = a := by
      rw [show ρ + l • e + a • f₁ + b • f₂ - ρ = l • e + (a • f₁ + b • f₂) by abel]
      simp [add_dotProduct, smul_dotProduct, h01, h11, s.2.2]
    have e2 : dotProduct (ρ + l • e + a • f₁ + b • f₂ - ρ) f₂ = b := by
      rw [show ρ + l • e + a • f₁ + b • f₂ - ρ = l • e + (a • f₁ + b • f₂) by abel]
      simp [add_dotProduct, smul_dotProduct, h02, h12, h22]
    rw [e1, e2]; exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    refine ⟨dotProduct (p - ρ) e, dotProduct (p - ρ) f₁, dotProduct (p - ρ) f₂, ha, hb, ?_⟩
    have := Orthonormal3.expand ⟨h00, h11, h22, h01, h02, h12⟩ (p - ρ)
    rw [add_assoc, add_assoc, ← add_assoc (dotProduct (p - ρ) e • e), ← this]
    abel

lemma tube_eq {ρ e f₁ f₂ : Fin 3 → ℝ} (h : Orthonormal3 e f₁ f₂) :
    tube ρ e f₁ f₂ = {p | |dotProduct (p - ρ) f₁| ≤ 1 / 2 ∧ |dotProduct (p - ρ) f₂| ≤ 1 / 2} := by
  ext p; exact mem_tube_iff h p

lemma isClosed_tube {ρ e f₁ f₂ : Fin 3 → ℝ} (h : Orthonormal3 e f₁ f₂) : IsClosed (tube ρ e f₁ f₂) := by
  rw [tube_eq h]
  apply IsClosed.inter
  · exact isClosed_le (f := fun p => |dotProduct (p - ρ) f₁|) (by simp only [dotProduct]; fun_prop)
      continuous_const
  · exact isClosed_le (f := fun p => |dotProduct (p - ρ) f₂|) (by simp only [dotProduct]; fun_prop)
      continuous_const

lemma measurableSet_tube {ρ e f₁ f₂ : Fin 3 → ℝ} (h : Orthonormal3 e f₁ f₂) :
    MeasurableSet (tube ρ e f₁ f₂) := (isClosed_tube h).measurableSet

lemma Orthonormal3.perm {v₀ v₁ v₂ : Fin 3 → ℝ} (h : Orthonormal3 v₀ v₁ v₂) : Orthonormal3 v₂ v₁ v₀ := by
  obtain ⟨s1, s2, s3⟩ := h.symm_dots
  obtain ⟨h00, h11, h22, _, _, _⟩ := h
  exact ⟨h22, h11, h00, s3, s2, s1⟩

lemma Orthonormal3.det_sq {v₀ v₁ v₂ : Fin 3 → ℝ} (h : Orthonormal3 v₀ v₁ v₂) :
    (rowsMat v₀ v₁ v₂).det ^ 2 = 1 := by
  have := congrArg Matrix.det h.mul_transpose
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  rw [sq]; exact this

/-- The coordinate equivalence `ℝ × ℝ × ℝ ≃ᵐ (Fin 3 → ℝ)`, `(a, b, c) ↦ ![a, b, c]`. -/
def coordEquiv : ℝ × ℝ × ℝ ≃ᵐ (Fin 3 → ℝ) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow.symm).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm

lemma coordEquiv_apply (x : ℝ × ℝ × ℝ) : coordEquiv x = ![x.1, x.2.1, x.2.2] := by
  ext i
  fin_cases i <;> rfl

lemma measurePreserving_coordEquiv : MeasurePreserving coordEquiv volume volume := by
  refine MeasurePreserving.trans ?_ (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
  exact (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ).symm

/-- The frame map `(g, s, l) ↦ ρ + l v₀ + s v₁ + g v₂`. -/
def framePsi (ρ v₀ v₁ v₂ : Fin 3 → ℝ) (x : ℝ × ℝ × ℝ) : Fin 3 → ℝ :=
  ρ + x.2.2 • v₀ + x.2.1 • v₁ + x.1 • v₂

lemma framePsi_eq (ρ v₀ v₁ v₂ : Fin 3 → ℝ) :
    framePsi ρ v₀ v₁ v₂ =
      (fun y => y + ρ) ∘ (Matrix.toLin' (rowsMat v₂ v₁ v₀).transpose) ∘ coordEquiv := by
  funext x j
  simp only [framePsi, Function.comp_apply, coordEquiv_apply, Matrix.toLin'_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply,
    rowsMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

lemma measurePreserving_framePsi {v₀ v₁ v₂ : Fin 3 → ℝ} (h : Orthonormal3 v₀ v₁ v₂) (ρ : Fin 3 → ℝ) :
    MeasurePreserving (framePsi ρ v₀ v₁ v₂) volume volume := by
  rw [framePsi_eq]
  set L := Matrix.toLin' (rowsMat v₂ v₁ v₀).transpose
  have hdet : LinearMap.det L ≠ 0 := by
    rw [LinearMap.det_toLin', Matrix.det_transpose]
    intro h0
    have := h.perm.det_sq
    rw [h0] at this; norm_num at this
  have habs : |(LinearMap.det L)⁻¹| = 1 := by
    rw [LinearMap.det_toLin', Matrix.det_transpose, abs_inv]
    have h2 := h.perm.det_sq
    have : |(rowsMat v₂ v₁ v₀).det| = 1 := by
      have h3 : |(rowsMat v₂ v₁ v₀).det| ^ 2 = 1 := by rw [sq_abs]; exact h2
      nlinarith [abs_nonneg (rowsMat v₂ v₁ v₀).det]
    rw [this, inv_one]
  have hL : MeasurePreserving L volume volume := by
    refine ⟨L.continuous_of_finiteDimensional.measurable, ?_⟩
    rw [MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet, habs,
      ENNReal.ofReal_one, one_smul]
  exact (measurePreserving_add_right volume ρ).comp (hL.comp measurePreserving_coordEquiv)

/-- **Fubini in an orthonormal frame.** -/
lemma volume_eq_iter {v₀ v₁ v₂ : Fin 3 → ℝ} (h : Orthonormal3 v₀ v₁ v₂) (ρ : Fin 3 → ℝ)
    {S : Set (Fin 3 → ℝ)} (hS : MeasurableSet S) :
    volume S = ∫⁻ g, ∫⁻ s, volume {l : ℝ | framePsi ρ v₀ v₁ v₂ (g, s, l) ∈ S} := by
  have hP := measurePreserving_framePsi h ρ
  rw [← hP.measure_preimage hS.nullMeasurableSet]
  have hm : MeasurableSet (framePsi ρ v₀ v₁ v₂ ⁻¹' S) := hP.measurable hS
  rw [Measure.volume_eq_prod, Measure.prod_apply hm]
  refine lintegral_congr fun g => ?_
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurable_prodMk_left hm)]
  rfl

end Sofa3D
