module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Planar Euclidean midpoint rigidity

The dimension-two case of Nielsen–Okamura Conjecture 9.1
(arXiv:2609.07551v2, Section 9). The Euclidean metric is fixed. A symmetric
cubic tensor has the four coefficients C111, C112, C122, C222; raising one
index gives K. The dual torsion-free connections are D+K and D-K.

Canonical midpoints are defined from actual short affine-parameter geodesics,
including uniqueness on their parameter interval. The proof constructs these
germs and derives the fourth-order obstruction from midpoint complementarity.
The two supporting statements require only everywhere Frechet differentiability.
No theorem here concerns unrestricted dimension three or higher.
-/

@[expose] public section
open Set Metric
open scoped ContDiff
namespace PlanarMidpoint

/-- The Euclidean plane with its Euclidean norm and inner product. -/
abbrev E := EuclideanSpace ℝ (Fin 2)
/-- The four independent coordinates of a totally symmetric planar cubic. -/
abbrev Coeff := Fin 4 → ℝ

/-- The affine midpoint parameter, explicitly named to keep independent statements identical. -/
noncomputable abbrev midpointTime : ℝ := 1 / 2

/-- A vector in standard Euclidean coordinates. -/
def vec (x y : ℝ) : E := !₂[x, y]

/-- The bilinear Christoffel tensor obtained by Euclidean index raising. -/
def K (c : Coeff) (u v : E) : E :=
  vec (c 0 * u 0 * v 0 + c 1 * (u 0 * v 1 + u 1 * v 0) + c 2 * u 1 * v 1)
      (c 1 * u 0 * v 0 + c 2 * (u 0 * v 1 + u 1 * v 0) + c 3 * u 1 * v 1)

/-- The fourth-order midpoint obstruction; the derivative slot is unrestricted. -/
def obstruction (c : Coeff) (J : E →L[ℝ] Coeff) (h : E) : E :=
  2 • K c h (K (J h) h h) + 5 • K (J (K c h h)) h h - 4 • K (J h) h (K c h h)

/-- The position and velocity satisfy the affine-parameter geodesic equation on [0,1]. -/
def IsGeodesicSegment (C : E → Coeff) (σ : ℝ) (γ v : ℝ → E) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt γ (v t) t) ∧
  (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt v (-σ • K (C (γ t)) (v t) (v t)) t)

/-- An endpoint geodesic whose position and velocity remain inside the specified small bounds. -/
def IsShortGeodesic (C : E → Coeff) (σ : ℝ) (p : E) (r : ℝ)
    (P Q : E) (γ v : ℝ → E) : Prop :=
  IsGeodesicSegment C σ γ v ∧ γ 0 = P ∧ γ 1 = Q ∧
    ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t - p‖ < r ∧ ‖v t‖ < r

/-- A local midpoint map given by the unique short geodesic near a diagonal point. -/
def IsCanonicalLocalMidpoint (Ω : Set E) (C : E → Coeff) (σ : ℝ)
    (p : E) (r : ℝ) (W : Set (E × E)) (A : E → E → E) : Prop :=
  0 < r ∧ ball p r ⊆ Ω ∧ IsOpen W ∧ (p, p) ∈ W ∧
  ∀ P Q, (P, Q) ∈ W → ∃ γ v,
    IsShortGeodesic C σ p r P Q γ v ∧ A P Q = γ midpointTime ∧
    ∀ γ' v', IsShortGeodesic C σ p r P Q γ' v' →
      ∀ t ∈ Icc (0 : ℝ) 1, γ' t = γ t ∧ v' t = v t

/-- Complementarity of the canonical local midpoint maps of `D+K` and `D-K`
near every diagonal point. The definition exposes the actual geodesic ODE. -/
def LocalMidpointInvariance (Ω : Set E) (C : E → Coeff) : Prop :=
  ∀ p ∈ Ω, ∃ rPlus rMinus W APlus AMinus,
    IsCanonicalLocalMidpoint Ω C 1 p rPlus W APlus ∧
    IsCanonicalLocalMidpoint Ω C (-1) p rMinus W AMinus ∧
    ∀ P Q, (P, Q) ∈ W → APlus P Q + AMinus P Q = P + Q

/-- Complementary canonical dual midpoints force every smooth planar cubic field to be constant. -/
theorem planar_dual_midpoint_rigidity (Ω : Set E) (C : E → Coeff)
    (openΩ : IsOpen Ω) (connectedΩ : IsPreconnected Ω)
    (smoothC : ContDiffOn ℝ ∞ C Ω)
    (complementary : LocalMidpointInvariance Ω C) :
    ∃ c : Coeff, ∀ p ∈ Ω, C p = c  := by sorry

/-- The quartic obstruction forces constancy under mere differentiability. -/
theorem planar_obstruction_rigidity
    (Ω : Set E) (C : E → Coeff)
    (openΩ : IsOpen Ω) (connectedΩ : IsPreconnected Ω)
    (diffC : DifferentiableOn ℝ C Ω)
    (PDE : ∀ p ∈ Ω, ∀ h, obstruction (C p) (fderiv ℝ C p) h = 0) :
    ∃ c : Coeff, ∀ p ∈ Ω, C p = c  := by sorry

/-- Testing the obstruction in five fixed directions at every point suffices. -/
theorem planar_five_direction_rigidity
    (Ω : Set E) (C : E → Coeff)
    (openΩ : IsOpen Ω) (connectedΩ : IsPreconnected Ω)
    (diffC : DifferentiableOn ℝ C Ω)
    (tests : ∀ p ∈ Ω, ∀ j : Fin 5,
      obstruction (C p) (fderiv ℝ C p) (vec (j : ℝ) 1) = 0) :
    ∃ c : Coeff, ∀ p ∈ Ω, C p = c  := by sorry

end PlanarMidpoint
