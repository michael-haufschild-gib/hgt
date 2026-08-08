/-
The Dirichlet leading-term interface is a graded leading-term interface.

`DirichletLead D` grades a ring of Dirichlet-type series by the least index `ord : D → ℕ`, which is
*multiplicative*: `ord (f * g) = ord f * ord g`, `ord (emb p) = 1`, and the shift acts on leading
coefficients through the scalar `ord f`.  `Rel.GradedLeadOver C Λ D` grades by a linearly ordered
abelian group `Λ` written additively, with the shift acting through a character `chi : Λ → C`.

The logarithm converts one into the other: `ord' := log ∘ ord` is additive on products, vanishes on
the index-one part, is order-preserving because `ord` is a positive natural, and the character
`chi t = exp t` reproduces the scalar `ord f`.  So a `DirichletLead` is a `GradedLeadOver ℂ ℝ`, and
the graded layer's theorems apply to Dirichlet-type series with no new hypotheses.

The two layers already carry the same two theorems (`ord_eq_of_rel`, `lead_shift_identity`) proved
independently; the bridge exhibits the Dirichlet copies as instances and, more usefully, transports
the graded layer's inertness capstone, which the Dirichlet layer never had:

* `dirichlet_defect_inert_over` — a rational function that is the translation defect of a quotient
  of Dirichlet-type series is already the translation defect of a rational function.
-/
import GaloisForLFunctions.HTGeometry.DirichletLeadingTerm
import GaloisForLFunctions.HTGeometry.RelativeGradedInertness

open Polynomial

namespace HTGeometry

namespace DirichletLead

variable {D : Type*} [CommRing D] (Dat : DirichletLead D)

/-- The least index of a nonzero element is a positive real. -/
theorem ordR_pos {f : D} (hf : f ≠ 0) : (0 : ℝ) < ((Dat.ord f : ℕ) : ℝ) := by
  exact_mod_cast Dat.ord_pos hf

/-- The logarithm is injective on the least indices of nonzero elements. -/
theorem ord_eq_of_logEq {f g : D} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : Real.log ((Dat.ord f : ℕ) : ℝ) = Real.log ((Dat.ord g : ℕ) : ℝ)) :
    Dat.ord f = Dat.ord g := by
  have hf' := Real.exp_log (Dat.ordR_pos hf)
  have hg' := Real.exp_log (Dat.ordR_pos hg)
  have hcast : ((Dat.ord f : ℕ) : ℝ) = ((Dat.ord g : ℕ) : ℝ) := by
    rw [← hf', ← hg', h]
  exact_mod_cast hcast

/-- The logarithm is strictly monotone on the least indices of nonzero elements. -/
theorem ord_lt_of_logLt {f g : D} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : Real.log ((Dat.ord f : ℕ) : ℝ) < Real.log ((Dat.ord g : ℕ) : ℝ)) :
    Dat.ord f < Dat.ord g := by
  have hf' := Real.exp_log (Dat.ordR_pos hf)
  have hg' := Real.exp_log (Dat.ordR_pos hg)
  have hcast : ((Dat.ord f : ℕ) : ℝ) < ((Dat.ord g : ℕ) : ℝ) := by
    rw [← hf', ← hg']
    exact Real.exp_lt_exp.mpr h
  exact_mod_cast hcast

/-- **A Dirichlet leading-term datum is a graded leading-term datum over `ℂ`, graded by `ℝ`.**
The grading is the logarithm of the least index and the character is the exponential, so the shift
scalar `ord f` is reproduced exactly. -/
noncomputable def toGradedLeadOver : Rel.GradedLeadOver ℂ ℝ D where
  sigma := Dat.sigma
  ord := fun f => Real.log ((Dat.ord f : ℕ) : ℝ)
  lead := Dat.lead
  emb := Dat.emb
  chi := fun t => ((Real.exp t : ℝ) : ℂ)
  chi_zero := by simp
  chi_add := by
    intro a b
    rw [Real.exp_add]
    push_cast
    ring
  chi_ne_zero := by
    intro a
    simp
  chi_injective := by
    intro a b h
    have h' : ((Real.exp a : ℝ) : ℂ) = ((Real.exp b : ℝ) : ℂ) := h
    have hr : Real.exp a = Real.exp b := by exact_mod_cast h'
    have := congrArg Real.log hr
    rwa [Real.log_exp, Real.log_exp] at this
  lead_zero := Dat.lead_zero
  lead_ne_zero := Dat.lead_ne_zero
  ord_mul := by
    intro f g hf hg
    rw [Dat.ord_mul hf hg]
    push_cast
    rw [Real.log_mul (Dat.ordR_pos hf).ne' (Dat.ordR_pos hg).ne']
  lead_mul := Dat.lead_mul
  sigma_ne_zero := Dat.sigma_ne_zero
  ord_sigma := by
    intro f hf
    rw [Dat.ord_sigma hf]
  lead_sigma := by
    intro f hf
    have hchi : ((Real.exp (Real.log ((Dat.ord f : ℕ) : ℝ)) : ℝ) : ℂ)
        = ((Dat.ord f : ℕ) : ℂ) := by
      rw [Real.exp_log (Dat.ordR_pos hf)]
      push_cast
      ring
    have h := Dat.lead_sigma hf
    rw [← hchi] at h
    exact h
  le_ord_sub := by
    intro f g hf hg hord hfg
    have hordN : Dat.ord f = Dat.ord g := Dat.ord_eq_of_logEq hf hg hord
    have hle := Dat.le_ord_sub hf hg hordN hfg
    have hcast : ((Dat.ord f : ℕ) : ℝ) ≤ ((Dat.ord (f - g) : ℕ) : ℝ) := by exact_mod_cast hle
    exact Real.log_le_log (Dat.ordR_pos hf) hcast
  lead_sub := by
    intro f g hf hg hord hsub
    rcases eq_or_ne (f - g) 0 with h0 | h0
    · have hfg : f = g := sub_eq_zero.mp h0
      rw [h0, Dat.lead_zero, hfg, sub_self]
    · have hordN : Dat.ord f = Dat.ord g := Dat.ord_eq_of_logEq hf hg hord
      have hsubN : Dat.ord (f - g) = Dat.ord f := Dat.ord_eq_of_logEq h0 hf hsub
      exact Dat.lead_sub hf hg hordN hsubN
  lead_eq_of_ord_lt := by
    intro f g hf hg hord hlt
    rcases eq_or_ne (f - g) 0 with h0 | h0
    · have hfg : f = g := sub_eq_zero.mp h0
      rw [hfg]
    · have hordN : Dat.ord f = Dat.ord g := Dat.ord_eq_of_logEq hf hg hord
      have hltN : Dat.ord f < Dat.ord (f - g) := Dat.ord_lt_of_logLt hf h0 hlt
      exact Dat.lead_eq_of_ord_lt hf hg hordN hltN
  sigma_emb := Dat.sigma_emb
  emb_ne_zero := Dat.emb_ne_zero
  ord_emb := by
    intro p hp
    rw [Dat.ord_emb hp]
    simp
  lead_emb := Dat.lead_emb

@[simp] theorem toGradedLeadOver_sigma : Dat.toGradedLeadOver.sigma = Dat.sigma := rfl

@[simp] theorem toGradedLeadOver_lead : Dat.toGradedLeadOver.lead = Dat.lead := rfl

@[simp] theorem toGradedLeadOver_emb : Dat.toGradedLeadOver.emb = Dat.emb := rfl

end DirichletLead

/-- **Leading-term inertness for Dirichlet-type series.**  A rational function which is the
translation defect of a quotient of Dirichlet-type series is already the translation defect of a
rational function in the shift coordinate.  This is the graded inertness capstone read through the
logarithmic grading, so no analytic input is added. -/
theorem dirichlet_defect_inert_over
    {K : Type*} [Field K] [Algebra ℂ K] {x : K} (hx : Transcendental ℂ x)
    (sigma : K ≃ₐ[ℂ] K) (hsig : sigma x = x + 1)
    {D : Type*} [CommRing D] (Dat : DirichletLead D)
    (phi : D →+* K) (hinj : Function.Injective phi)
    (hphisigma : ∀ f : D, phi (Dat.sigma f) = sigma (phi f))
    (hphiemb : ∀ p : ℂ[X], phi (Dat.emb p) = Polynomial.aeval x p)
    {P Q : D} (hQ : Q ≠ 0) {v : K} (hv : v ∈ Rel.coordBaseOver ℂ x)
    (hdef : sigma (phi P / phi Q) - phi P / phi Q = v) :
    ∃ R ∈ Rel.coordBaseOver ℂ x, sigma R - R = v :=
  Rel.graded_defect_inert_over hx sigma hsig Dat.toGradedLeadOver phi hinj hphisigma hphiemb hQ hv
    hdef

end HTGeometry
