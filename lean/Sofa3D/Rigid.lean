import Sofa3D.Tilt

/-!
# Rigid motions: tubes, volume

A motion `p ↦ R p + v` with `Rᵀ R = 1` preserves dot products, maps tubes to tubes, and (with `|det R| = 1`)
preserves volume. The tubes `X = ℝ × [0, 1]²` and `Y = [0, 1] × ℝ × [0, 1]`.
-/

open MeasureTheory Set

namespace Sofa3D

lemma dot_mulVec_mulVec {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R.transpose * R = 1) (a b : Fin 3 → ℝ) :
    dotProduct (Matrix.mulVec R a) (Matrix.mulVec R b) = dotProduct a b := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]

lemma Orthonormal3.mulVec {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R.transpose * R = 1) {v₀ v₁ v₂ : Fin 3 → ℝ}
    (h : Orthonormal3 v₀ v₁ v₂) :
    Orthonormal3 (Matrix.mulVec R v₀) (Matrix.mulVec R v₁) (Matrix.mulVec R v₂) := by
  obtain ⟨h00, h11, h22, h01, h02, h12⟩ := h
  simp only [Orthonormal3, dot_mulVec_mulVec hR]
  exact ⟨h00, h11, h22, h01, h02, h12⟩

lemma motion_image_tube (g : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)) (ρ e f₁ f₂ : Fin 3 → ℝ) :
    motion g '' tube ρ e f₁ f₂ =
      tube (motion g ρ) (Matrix.mulVec g.1 e) (Matrix.mulVec g.1 f₁) (Matrix.mulVec g.1 f₂) := by
  ext p
  constructor
  · rintro ⟨q, ⟨l, a, b, ha, hb, rfl⟩, rfl⟩
    refine ⟨l, a, b, ha, hb, ?_⟩
    simp only [motion, Matrix.mulVec_add, Matrix.mulVec_smul]
    abel
  · rintro ⟨l, a, b, ha, hb, rfl⟩
    refine ⟨ρ + l • e + a • f₁ + b • f₂, ⟨l, a, b, ha, hb, rfl⟩, ?_⟩
    simp only [motion, Matrix.mulVec_add, Matrix.mulVec_smul]
    abel

lemma measurePreserving_motion (g : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)) (hdet : |g.1.det| = 1) :
    MeasurePreserving (motion g) volume volume := by
  have hfun : motion g = (fun y => y + g.2) ∘ Matrix.toLin' g.1 := by
    funext p; simp [motion, Matrix.toLin'_apply]
  rw [hfun]
  set L := Matrix.toLin' g.1
  have hdet' : LinearMap.det L ≠ 0 := by
    rw [LinearMap.det_toLin']; intro h0; rw [h0, abs_zero] at hdet; exact zero_ne_one hdet
  have hL : MeasurePreserving L volume volume := by
    refine ⟨L.continuous_of_finiteDimensional.measurable, ?_⟩
    rw [MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet', LinearMap.det_toLin',
      abs_inv, hdet, inv_one, ENNReal.ofReal_one, one_smul]
  exact (measurePreserving_add_right volume g.2).comp hL

/-- The inverse motion. -/
def motionInv (g : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)) : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ) :=
  (g.1.transpose, -(Matrix.mulVec g.1.transpose g.2))

lemma motion_image_eq_preimage (g : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ))
    (h1 : g.1.transpose * g.1 = 1) (h2 : g.1 * g.1.transpose = 1) (S : Set (Fin 3 → ℝ)) :
    motion g '' S = motion (motionInv g) ⁻¹' S := by
  ext p
  simp only [mem_image, mem_preimage, motion, motionInv]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    simpa using hq
  · intro hp
    refine ⟨_, hp, ?_⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2,
      Matrix.one_mulVec, Matrix.one_mulVec]
    abel

lemma volume_motion_image (g : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ))
    (hg : g.1 ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) {S : Set (Fin 3 → ℝ)} (hS : MeasurableSet S) :
    volume (motion g '' S) = volume S := by
  have hg' := Matrix.mem_specialOrthogonalGroup_iff.mp hg
  have h2 : g.1 * g.1.transpose = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp hg'.1
  have h1 : g.1.transpose * g.1 = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hg'.1
  rw [motion_image_eq_preimage g h1 h2]
  have hdet : |(motionInv g).1.det| = 1 := by
    simp only [motionInv, Matrix.det_transpose]; rw [hg'.2, abs_one]
  exact (measurePreserving_motion _ hdet).measure_preimage hS.nullMeasurableSet

/-- The tube `X = ℝ × [0, 1] × [0, 1]`. -/
def Xt : Set (Fin 3 → ℝ) := {p | 0 ≤ p 1 ∧ p 1 ≤ 1 ∧ 0 ≤ p 2 ∧ p 2 ≤ 1}

/-- The tube `Y = [0, 1] × ℝ × [0, 1]`. -/
def Yt : Set (Fin 3 → ℝ) := {p | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 2 ∧ p 2 ≤ 1}

lemma orthonormal_xyz : Orthonormal3 ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] := by
  simp [Orthonormal3, dotProduct_fin3]

lemma orthonormal_yxz : Orthonormal3 ![0, 1, 0] ![1, 0, 0] ![0, 0, 1] := by
  simp [Orthonormal3, dotProduct_fin3]

lemma abs_sub_half_le_iff (x : ℝ) : |x - 2⁻¹| ≤ 2⁻¹ ↔ 0 ≤ x ∧ x ≤ 1 := by
  rw [abs_le]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma Xt_eq : Xt = tube ![0, 1 / 2, 1 / 2] ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] := by
  ext p
  rw [mem_tube_iff orthonormal_xyz]
  simp only [Xt, mem_ofPred_eq, dotProduct_fin3, Pi.sub_apply]
  simp [abs_sub_half_le_iff, and_assoc]
  try (simp only [abs_sub_half_le_iff, and_assoc])

lemma Yt_eq : Yt = tube ![1 / 2, 0, 1 / 2] ![0, 1, 0] ![1, 0, 0] ![0, 0, 1] := by
  ext p
  rw [mem_tube_iff orthonormal_yxz]
  simp only [Yt, mem_ofPred_eq, dotProduct_fin3, Pi.sub_apply]
  simp [abs_sub_half_le_iff, and_assoc]
  try (simp only [abs_sub_half_le_iff, and_assoc])

end Sofa3D
