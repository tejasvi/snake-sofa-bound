import Sofa3D.TwoTube
import Sofa3D.Rigid

/-!
# The corridor near the first turn, composition of motions, and the reduction to `g₀ = id`
-/

open MeasureTheory Set

namespace Sofa3D

/-! ## Set facts -/

lemma SX_sub_Xt : SX ⊆ Xt := fun p ⟨_, h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩

lemma SYc_sub_Yt (c : ℝ) : SYc c ⊆ Yt := fun p ⟨h0, h1, _, _, h3, h4⟩ => ⟨h0, h1, h3, h4⟩

/-- (2.1): `K_M ∩ {y ≤ c} ⊆ S_X ∪ S_Y(c)` for `c < 1 + M`. -/
lemma corridor_le {M c : ℝ} (hc : c < 1 + M) {p : Fin 3 → ℝ} (hp : p ∈ corridor M) (hpc : p 1 ≤ c) :
    p ∈ SX ∪ SYc c := by
  rcases hp with (hp | hp) | hp
  · exact Or.inl hp
  · obtain ⟨h0, h1, h2, _, h4, h5⟩ := hp
    exact Or.inr ⟨h0, h1, h2, hpc, h4, h5⟩
  · obtain ⟨_, _, h2, _, _⟩ := hp
    exact absurd (lt_of_lt_of_le hc h2) (not_lt.mpr hpc)

/-- `K_M ∩ {y ≤ 1} ⊆ X` for `M > 0`. -/
lemma corridor_le_one_sub_Xt {M : ℝ} (hM : 0 < M) {p : Fin 3 → ℝ} (hp : p ∈ corridor M) (hp1 : p 1 ≤ 1) :
    p ∈ Xt := by
  rcases hp with (hp | hp) | hp
  · exact SX_sub_Xt hp
  · obtain ⟨_, _, h2, _, h4, h5⟩ := hp
    exact ⟨h2, hp1, h4, h5⟩
  · obtain ⟨_, _, h2, _, _⟩ := hp
    linarith

/-! ## Composition of motions -/

/-- The composition `motion (mcomp g h) = motion g ∘ motion h`. -/
def mcomp (g h : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)) : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ) :=
  (g.1 * h.1, Matrix.mulVec g.1 h.2 + g.2)

lemma motion_mcomp (g h : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)) (p : Fin 3 → ℝ) :
    motion (mcomp g h) p = motion g (motion h p) := by
  simp only [motion, mcomp, Matrix.mulVec_add, Matrix.mulVec_mulVec]
  abel

lemma motionInv_motion (g : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)) (h1 : g.1.transpose * g.1 = 1)
    (p : Fin 3 → ℝ) : motion (motionInv g) (motion g p) = p := by
  simp only [motion, motionInv, Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  abel

lemma transpose_mem_SO {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    A.transpose ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  have hA' := Matrix.mem_specialOrthogonalGroup_iff.mp hA
  refine Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff, Matrix.transpose_transpose]
    exact (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hA'.1
  · rw [Matrix.det_transpose]; exact hA'.2

lemma SO_transpose_mul {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    A.transpose * A = 1 :=
  (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp (Matrix.mem_specialOrthogonalGroup_iff.mp hA).1

lemma SO_mul_transpose {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    A * A.transpose = 1 :=
  (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp (Matrix.mem_specialOrthogonalGroup_iff.mp hA).1

lemma continuous_motion_joint : Continuous fun x : (Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)) × (Fin 3 → ℝ) =>
    motion x.1 x.2 := by
  unfold motion
  exact (continuous_fst.fst.matrix_mulVec continuous_snd).add continuous_fst.snd

lemma isBody_image {B : Set (Fin 3 → ℝ)} (hB : IsBody B) (g : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)) :
    IsBody (motion g '' B) := by
  have hc : Continuous (motion g) :=
    continuous_motion_joint.comp (continuous_const.prodMk continuous_id)
  exact ⟨hB.1.image hc, hB.2.image _ hc.continuousOn⟩

/-- **Reduction to `g₀ = id`.** A weak passage of `B` gives a weak passage of `B₀ = g₀(B)` whose rotation part
at time `0` is the identity, with the same positions `B_t`. -/
lemma reduce_start {M : ℝ} {B : Set (Fin 3 → ℝ)} {g : unitInterval → Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)}
    (hg : IsWeakPassage M B g) :
    IsWeakPassage M (motion (g 0) '' B) (fun t => mcomp (g t) (motionInv (g 0))) ∧
      (mcomp (g 0) (motionInv (g 0))).1 = 1 ∧
      (∀ t, motion (mcomp (g t) (motionInv (g 0))) '' (motion (g 0) '' B) = motion (g t) '' B) := by
  have h0 := SO_transpose_mul (hg.rotation 0)
  have himg : ∀ t, motion (mcomp (g t) (motionInv (g 0))) '' (motion (g 0) '' B) = motion (g t) '' B := by
    intro t
    rw [image_image]
    congr 1
    funext q
    rw [motion_mcomp, motionInv_motion _ h0]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, himg⟩
  · unfold mcomp
    have hc := hg.continuous
    refine ((hc.fst).mul continuous_const).prodMk (((hc.fst).matrix_mulVec continuous_const).add hc.snd)
  · intro t
    exact Submonoid.mul_mem _ (hg.rotation t) (transpose_mem_SO (hg.rotation 0))
  · intro t; rw [himg t]; exact hg.inside t
  · rw [himg 0]; exact hg.start
  · rw [himg 1]; exact hg.finish
  · simp only [mcomp, motionInv]; exact SO_mul_transpose (hg.rotation 0)

end Sofa3D
