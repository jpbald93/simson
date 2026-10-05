import Simson.Basic

/-!
# The algebraic core of the Simson line

`area2 (feet) * D₁ D₂ D₃ = area2(A,B,C)² * K(A,B,C,P)` where `K` is the
concyclicity determinant (written out by cofactor expansion along the `x²+y²` column).
-/

noncomputable section

namespace Simson

/-- Concyclicity determinant `det [[x, y, x²+y², 1]]` of four points
(expanded along the third column). It vanishes iff the points are concyclic or collinear. -/
def concyc (a b c p : ℂ) : ℝ :=
  (b.re * c.im - b.re * p.im - b.im * c.re + b.im * p.re + c.re * p.im - c.im * p.re) *
      (a.re ^ 2 + a.im ^ 2) +
    (-a.re * c.im + a.re * p.im + a.im * c.re - a.im * p.re - c.re * p.im + c.im * p.re) *
      (b.re ^ 2 + b.im ^ 2) +
    (a.re * b.im - a.re * p.im - a.im * b.re + a.im * p.re + b.re * p.im - b.im * p.re) *
      (c.re ^ 2 + c.im ^ 2) +
    (-a.re * b.im + a.re * c.im + a.im * b.re - a.im * c.re - b.re * c.im + b.im * c.re) *
      (p.re ^ 2 + p.im ^ 2)

/-- If the four points lie on a common circle, the concyclicity determinant vanishes. -/
lemma concyc_eq_zero_of_dist {a b c p o : ℂ} {r : ℝ}
    (ha : dist a o = r) (hb : dist b o = r) (hc : dist c o = r) (hp : dist p o = r) :
    concyc a b c p = 0 := by
  have ga := dist_sq_re_im a o
  have gb := dist_sq_re_im b o
  have gc := dist_sq_re_im c o
  have gp := dist_sq_re_im p o
  rw [ha] at ga; rw [hb] at gb; rw [hc] at gc; rw [hp] at gp
  unfold concyc
  linear_combination
    (-(b.re * c.im - b.re * p.im - b.im * c.re + b.im * p.re + c.re * p.im - c.im * p.re)) * ga -
    (-a.re * c.im + a.re * p.im + a.im * c.re - a.im * p.re - c.re * p.im + c.im * p.re) * gb -
    (a.re * b.im - a.re * p.im - a.im * b.re + a.im * p.re + b.re * p.im - b.im * p.re) * gc -
    (-a.re * b.im + a.re * c.im + a.im * b.re - a.im * c.re - b.re * c.im + b.im * c.re) * gp

/-- The key identity: the signed area of the pedal triangle of `p`, cleared of denominators. -/
theorem area2_perpFoot_mul {a b c : ℂ} (p : ℂ) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    area2 (perpFoot p b c) (perpFoot p c a) (perpFoot p a b) *
        (((c.re - b.re) ^ 2 + (c.im - b.im) ^ 2) * ((a.re - c.re) ^ 2 + (a.im - c.im) ^ 2) *
          ((b.re - a.re) ^ 2 + (b.im - a.im) ^ 2)) =
      area2 a b c ^ 2 * concyc a b c p := by
  have h1 := sqD_ne_zero hbc
  have h2 := sqD_ne_zero hca
  have h3 := sqD_ne_zero hab
  simp only [area2, concyc, perpFoot_re, perpFoot_im, footParam]
  field_simp
  ring

end Simson
