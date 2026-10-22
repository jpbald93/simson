import Simson.Basic
import Simson.Identity
import Simson.Main
import Simson.Bridge
import Simson.L14
import Mathlib

/-!
# Layer 15: independent classical statements

Layer 15. These definitions and statements were written independently, from textbook statements,
by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves
(or proves part of) one of them from this development.

Comparison of the writer statements `classical_A3_*` vs. the Simson library.
-/

open EuclideanGeometry

noncomputable section

namespace Simson.Classical

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-! Writer's statements, verbatim, packaged as `Prop`s. -/

def classical_A3_a : Prop :=
  ∀ (A B C P : Plane) (h : AffineIndependent ℝ ![A, B, C])
    (_hP : P ∈ (⟨![A, B, C], h⟩ : Affine.Triangle ℝ Plane).circumsphere),
    Collinear ℝ ({(orthogonalProjection line[ℝ, B, C] P : Plane),
      (orthogonalProjection line[ℝ, C, A] P : Plane),
      (orthogonalProjection line[ℝ, A, B] P : Plane)} : Set Plane)

def classical_A3_b : Prop :=
  ∀ (A B C P : Plane) (h : AffineIndependent ℝ ![A, B, C])
    (_hcol : Collinear ℝ ({(orthogonalProjection line[ℝ, B, C] P : Plane),
      (orthogonalProjection line[ℝ, C, A] P : Plane),
      (orthogonalProjection line[ℝ, A, B] P : Plane)} : Set Plane)),
    P ∈ (⟨![A, B, C], h⟩ : Affine.Triangle ℝ Plane).circumsphere

/-! ## Glue -/

/-- The isometry `ℂ ≃ ℝ²` (`z ↦ ![re z, im z]`). -/
abbrev e : ℂ ≃ₗᵢ[ℝ] Plane := Complex.orthonormalBasisOneI.repr

lemma collinear_image {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) {s : Set V} (h : Collinear ℝ s) : Collinear ℝ (f '' s) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h ⊢
  obtain ⟨p₀, v, hv⟩ := h
  refine ⟨f p₀, f v, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨r, rfl⟩ := hv p hp
  exact ⟨r, by simp [vadd_eq_add]⟩

lemma proj_eq_of_map (s : AffineSubspace ℝ ℂ) [Nonempty s] [s.direction.HasOrthogonalProjection]
    (s' : AffineSubspace ℝ Plane) [Nonempty s'] [s'.direction.HasOrthogonalProjection]
    (f : ℂ →ᵃⁱ[ℝ] Plane) (hs : s.map f.toAffineMap = s') (p : ℂ) :
    (orthogonalProjection s' (f p) : Plane) = f (orthogonalProjection s p) := by
  subst hs
  exact orthogonalProjection_map s f p

/-- Orthogonal projection onto a line commutes with `e`. -/
lemma proj_e (u v p : ℂ) :
    (orthogonalProjection line[ℝ, e u, e v] (e p) : Plane) =
      e (orthogonalProjection line[ℝ, u, v] p) := by
  have := proj_eq_of_map line[ℝ, u, v] line[ℝ, e u, e v]
    e.toAffineIsometryEquiv.toAffineIsometry (by
      rw [AffineSubspace.map_span]; simp [Set.image_insert_eq]) p
  simpa using this

/-- NEW: the missing converse bridge, `Collinear → area2 = 0`. -/
lemma area2_eq_zero_of_collinear {x y z : ℂ} (h : Collinear ℝ ({x, y, z} : Set ℂ)) :
    Simson.area2 x y z = 0 := by
  rw [collinear_iff_of_mem (p₀ := x) (by simp)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨s, hs⟩ := hv y (by simp)
  obtain ⟨t, ht⟩ := hv z (by simp)
  rw [hs, ht]
  simp only [Simson.area2, vadd_eq_add, Complex.add_re, Complex.add_im, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- A point equidistant (with the triangle's vertices) from some centre lies on the
circumsphere (plane case: the centre is automatically in the affine span). -/
lemma mem_circumsphere_of_dist (T : Affine.Triangle ℝ Plane) (P c : Plane) (r : ℝ)
    (hr : ∀ i, dist (T.points i) c = r) (hP : dist P c = r) : P ∈ T.circumsphere := by
  have hspan : affineSpan ℝ (Set.range T.points) = ⊤ :=
    T.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)
  have hc : c ∈ affineSpan ℝ (Set.range T.points) := by rw [hspan]; trivial
  have h1 := T.eq_circumcenter_of_dist_eq hc hr
  have h2 := T.eq_circumradius_of_dist_eq hc hr
  rw [EuclideanGeometry.mem_sphere, Affine.Simplex.circumsphere_center,
    Affine.Simplex.circumsphere_radius, ← h1, ← h2, hP]

lemma ne_of_indep {a b c : ℂ} (h : AffineIndependent ℝ ![e a, e b, e c]) :
    a ≠ b ∧ b ≠ c ∧ c ≠ a := by
  have h01 := h.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have h12 := h.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have h20 := h.injective.ne (show (2 : Fin 3) ≠ 0 by decide)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, ne_eq] at h01 h12 h20
  exact ⟨fun h => h01 (by rw [h]), fun h => h12 (by rw [h]), fun h => h20 (by rw [h])⟩

/-! ## Comparisons -/

/-- (E) A3(a), from `Simson.simson` + `Simson.perpFoot_eq_orthogonalProjection`. -/
theorem cov_A3_a : classical_A3_a := by
  intro A B C P h hP
  obtain ⟨a, rfl⟩ := e.surjective A
  obtain ⟨b, rfl⟩ := e.surjective B
  obtain ⟨c, rfl⟩ := e.surjective C
  obtain ⟨p, rfl⟩ := e.surjective P
  obtain ⟨hab, hbc, hca⟩ := ne_of_indep h
  set T : Affine.Triangle ℝ Plane := ⟨![e a, e b, e c], h⟩
  have hd : ∀ x : ℂ, e x ∈ T.circumsphere → dist x (e.symm T.circumcenter) = T.circumradius := by
    intro x hx
    rw [EuclideanGeometry.mem_sphere, Affine.Simplex.circumsphere_center,
      Affine.Simplex.circumsphere_radius] at hx
    rw [← hx, ← e.dist_map, e.apply_symm_apply]
  have hcirc : Cospherical ({a, b, c, p} : Set ℂ) := by
    refine ⟨e.symm T.circumcenter, T.circumradius, ?_⟩
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hd _ (T.mem_circumsphere 0)
    · exact hd _ (T.mem_circumsphere 1)
    · exact hd _ (T.mem_circumsphere 2)
    · exact hd _ hP
  have hcol := Simson.simson hab hbc hca hcirc
  simp only [Simson.perpFoot_eq_orthogonalProjection] at hcol
  have := collinear_image e.toLinearEquiv.toLinearMap hcol
  simp only [Set.image_insert_eq, Set.image_singleton, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv] at this
  simp only [proj_e]
  exact this

/-- (O, closed by NEW PROOF) A3(b), the geometric converse: from
`Simson.area2_perpFoot_eq_zero_iff`, `Simson.concyc_eq_zero_iff_cospherical`, and the new
bridge `area2_eq_zero_of_collinear`. -/
theorem cov_A3_b : classical_A3_b := by
  intro A B C P h hcol
  obtain ⟨a, rfl⟩ := e.surjective A
  obtain ⟨b, rfl⟩ := e.surjective B
  obtain ⟨c, rfl⟩ := e.surjective C
  obtain ⟨p, rfl⟩ := e.surjective P
  simp only [proj_e] at hcol
  have hcol' := collinear_image e.symm.toLinearEquiv.toLinearMap hcol
  simp only [Set.image_insert_eq, Set.image_singleton] at hcol'
  simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.symm_apply_apply] at hcol'
  simp only [← Simson.perpFoot_eq_orthogonalProjection] at hcol'
  have habc : Simson.area2 a b c ≠ 0 := by
    intro h0
    have := collinear_image e.toLinearEquiv.toLinearMap (Simson.collinear_of_area2_eq_zero h0)
    simp only [Set.image_insert_eq, Set.image_singleton, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv] at this
    exact (affineIndependent_iff_not_collinear_set.mp h) this
  have hk := (Simson.area2_perpFoot_eq_zero_iff p habc).mp (area2_eq_zero_of_collinear hcol')
  obtain ⟨o, r, hor⟩ := (Simson.concyc_eq_zero_iff_cospherical habc).mp hk
  refine mem_circumsphere_of_dist _ (e p) (e o) r ?_ (by rw [e.dist_map]; exact hor p (by simp))
  intro i
  fin_cases i
  · simpa [e.dist_map] using hor a (by simp)
  · simpa [e.dist_map] using hor b (by simp)
  · simpa [e.dist_map] using hor c (by simp)

end Simson.Classical
