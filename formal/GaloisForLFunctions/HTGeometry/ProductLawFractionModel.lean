import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import GaloisForLFunctions.HTGeometry.PolynomialCascadeModel

/-!
# The product law in the rational model

A cascade of first-order linear entire maps `f_k(w) = d_k + c_k·exp(A_k(w))` has states obeying

`δ X_(k+1) = A_k'(X_k)·(X_(k+1) − d_k)·δ X_k`,

so `δ X_k` is a product of univariate factors, one per coordinate:

`δ X_k = ∏_(j<k) g_j(X_j)`.

The polynomial ring is too small to run the Bell induction on such a law, because the logarithmic
derivative of the product involves `g_j'/g_j`.  The fraction field of the polynomial ring is the right
model: it is a domain, so algebraic independence transfers back, and there the logarithmic derivative
is an honest element,

`δ(δ X_k) = δ X_k · ∑_(j<k) (g_j'(X_j)/g_j(X_j))·δ X_j`.

This file sets up that model: the product law as a derivation of the fraction field, the coordinate
derivations, and the two identities the induction runs on.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The rational model of a cascade: the fraction field of the polynomial ring on the states. -/
abbrev CascadeField : Type := FractionRing (MvPolynomial ℕ ℂ)

/-- A coordinate of the rational model. -/
noncomputable def fx (k : ℕ) : CascadeField :=
  algebraMap (MvPolynomial ℕ ℂ) CascadeField (MvPolynomial.X k)

/-- A univariate polynomial evaluated at one coordinate. -/
noncomputable def univFactor (p : Polynomial ℂ) (j : ℕ) : MvPolynomial ℕ ℂ :=
  Polynomial.aeval (MvPolynomial.X j) p

/-- The image of a univariate factor in the rational model. -/
noncomputable def prodFactor (g : ℕ → Polynomial ℂ) (j : ℕ) : CascadeField :=
  algebraMap (MvPolynomial ℕ ℂ) CascadeField (univFactor (g j) j)

/-! ## Nonvanishing of the factors -/

/-- Evaluating a one-coordinate polynomial at a point of that coordinate returns the original
polynomial's value. -/
theorem aeval_univFactor (p : Polynomial ℂ) (j : ℕ) (t : ℂ) :
    MvPolynomial.aeval (fun i => if i = j then t else 0) (univFactor p j) = p.eval t := by
  rw [univFactor, ← Polynomial.aeval_algHom_apply]
  simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]

/-- A nonzero univariate polynomial gives a nonzero one-coordinate polynomial. -/
theorem univFactor_ne_zero {p : Polynomial ℂ} (hp : p ≠ 0) (j : ℕ) :
    univFactor p j ≠ 0 := by
  intro h0
  refine hp (Polynomial.funext fun t => ?_)
  have h := aeval_univFactor p j t
  rw [h0, map_zero] at h
  rw [Polynomial.eval_zero]
  exact h.symm

theorem prodFactor_ne_zero {g : ℕ → Polynomial ℂ} (hg : ∀ j, g j ≠ 0) (j : ℕ) :
    prodFactor g j ≠ 0 := by
  rw [prodFactor]
  intro h0
  refine univFactor_ne_zero (hg j) j ?_
  have hinj : Function.Injective
      (algebraMap (MvPolynomial ℕ ℂ) CascadeField) := IsFractionRing.injective _ _
  exact hinj (by rw [h0, map_zero])

/-! ## The product law -/

/-- The product appearing in the law: the jet of the `k`-th coordinate. -/
noncomputable def prodJet (g : ℕ → Polynomial ℂ) (k : ℕ) : CascadeField :=
  ∏ j ∈ Finset.range k, prodFactor g j

@[simp] theorem prodJet_zero (g : ℕ → Polynomial ℂ) : prodJet g 0 = 1 := by
  simp [prodJet]

theorem prodJet_succ (g : ℕ → Polynomial ℂ) (k : ℕ) :
    prodJet g (k + 1) = prodJet g k * prodFactor g k := by
  rw [prodJet, prodJet, Finset.prod_range_succ]

theorem prodJet_ne_zero {g : ℕ → Polynomial ℂ} (hg : ∀ j, g j ≠ 0) (k : ℕ) :
    prodJet g k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => prodFactor_ne_zero hg j

/-- The product law as a derivation of the polynomial ring into the rational model. -/
noncomputable def prodDerivationPoly (g : ℕ → Polynomial ℂ) :
    Derivation ℂ (MvPolynomial ℕ ℂ) CascadeField :=
  MvPolynomial.mkDerivation ℂ fun k => prodJet g k

@[simp] theorem prodDerivationPoly_X (g : ℕ → Polynomial ℂ) (k : ℕ) :
    prodDerivationPoly g (MvPolynomial.X k) = prodJet g k :=
  MvPolynomial.mkDerivation_X ℂ _ k

/-- **The product law on the rational model.** -/
noncomputable def prodDerivation (g : ℕ → Polynomial ℂ) :
    Derivation ℂ CascadeField CascadeField :=
  fractionRingDerivation (prodDerivationPoly g)

@[simp] theorem prodDerivation_fx (g : ℕ → Polynomial ℂ) (k : ℕ) :
    prodDerivation g (fx k) = prodJet g k := by
  rw [prodDerivation, fx, fractionRingDerivation_algebraMap, prodDerivationPoly_X]

/-! ## The chain rule for a univariate factor -/

/-- A derivation differentiates a one-coordinate polynomial by the chain rule. -/
theorem derivation_univFactor {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (MvPolynomial ℕ ℂ) M]
    [IsScalarTower ℂ (MvPolynomial ℕ ℂ) M]
    (D : Derivation ℂ (MvPolynomial ℕ ℂ) M) (p : Polynomial ℂ) (j : ℕ) :
    D (univFactor p j) = univFactor p.derivative j • D (MvPolynomial.X j) := by
  induction p using Polynomial.induction_on with
  | C a =>
      have h : univFactor (Polynomial.C a) j = MvPolynomial.C a := by
        simp [univFactor]
      rw [h, Polynomial.derivative_C]
      have h2 : univFactor (0 : Polynomial ℂ) j = 0 := by simp [univFactor]
      rw [h2, zero_smul,
        show (MvPolynomial.C a : MvPolynomial ℕ ℂ) = algebraMap ℂ (MvPolynomial ℕ ℂ) a from rfl,
        D.map_algebraMap]
  | add p q hp hq =>
      have hsum : univFactor (p + q) j = univFactor p j + univFactor q j := by
        simp [univFactor]
      rw [hsum, map_add, hp, hq, Polynomial.derivative_add]
      have hd : univFactor (p.derivative + q.derivative) j
          = univFactor p.derivative j + univFactor q.derivative j := by
        simp [univFactor]
      rw [hd, add_smul]
  | monomial n a ih =>
      have hmul : univFactor (Polynomial.C a * Polynomial.X ^ (n + 1)) j
          = MvPolynomial.C a * MvPolynomial.X j ^ (n + 1) := by
        simp [univFactor]
      have hder : (Polynomial.C a * Polynomial.X ^ (n + 1)).derivative
          = Polynomial.C ((n : ℂ) + 1) * (Polynomial.C a * Polynomial.X ^ n) := by
        rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow]
        simp only [Nat.add_sub_cancel]
        push_cast
        ring
      have hcoef : univFactor (Polynomial.C ((n : ℂ) + 1) * (Polynomial.C a * Polynomial.X ^ n)) j
          = MvPolynomial.C ((n : ℂ) + 1) * (MvPolynomial.C a * MvPolynomial.X j ^ n) := by
        simp [univFactor]
      have hCa : D (MvPolynomial.C a : MvPolynomial ℕ ℂ) = 0 := by
        rw [show (MvPolynomial.C a : MvPolynomial ℕ ℂ)
          = algebraMap ℂ (MvPolynomial ℕ ℂ) a from rfl]
        exact D.map_algebraMap a
      rw [hmul, hder, hcoef, Derivation.leibniz, hCa, smul_zero, add_zero,
        Derivation.leibniz_pow]
      have hnat : ((n + 1 : ℕ))
            • ((MvPolynomial.X j : MvPolynomial ℕ ℂ) ^ (n + 1 - 1) • D (MvPolynomial.X j))
          = (((n + 1 : ℕ) : MvPolynomial ℕ ℂ))
              • ((MvPolynomial.X j : MvPolynomial ℕ ℂ) ^ (n + 1 - 1) • D (MvPolynomial.X j)) :=
        (Nat.cast_smul_eq_nsmul (MvPolynomial ℕ ℂ) (n + 1)
          ((MvPolynomial.X j : MvPolynomial ℕ ℂ) ^ (n + 1 - 1) • D (MvPolynomial.X j))).symm
      rw [hnat, smul_smul, smul_smul]
      congr 1
      have hcast : ((n + 1 : ℕ) : MvPolynomial ℕ ℂ) = MvPolynomial.C ((n : ℂ) + 1) := by
        push_cast
        simp
      rw [hcast]
      simp only [Nat.add_sub_cancel]
      ring

/-! ## The logarithmic derivative of the product -/

/-- The logarithmic derivative of one factor. -/
noncomputable def logFactor (g : ℕ → Polynomial ℂ) (j : ℕ) : CascadeField :=
  algebraMap (MvPolynomial ℕ ℂ) CascadeField (univFactor (g j).derivative j) / prodFactor g j

/-- The logarithmic derivative of the whole product, weighted by the coordinate jets. -/
noncomputable def logSum (g : ℕ → Polynomial ℂ) (k : ℕ) : CascadeField :=
  ∑ j ∈ Finset.range k, logFactor g j * prodJet g j

@[simp] theorem logSum_zero (g : ℕ → Polynomial ℂ) : logSum g 0 = 0 := by
  simp [logSum]

theorem logSum_succ (g : ℕ → Polynomial ℂ) (k : ℕ) :
    logSum g (k + 1) = logSum g k + logFactor g k * prodJet g k := by
  rw [logSum, logSum, Finset.sum_range_succ]

/-- The derivation of a single factor. -/
theorem prodDerivation_prodFactor (g : ℕ → Polynomial ℂ) (k : ℕ) :
    prodDerivation g (prodFactor g k)
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField (univFactor (g k).derivative k)
        * prodJet g k := by
  rw [prodFactor, prodDerivation, fractionRingDerivation_algebraMap,
    derivation_univFactor (prodDerivationPoly g) (g k) k, prodDerivationPoly_X,
    Algebra.smul_def]

/-- **The logarithmic law of the product.**  The jet of a coordinate has logarithmic derivative equal
to the weighted sum of the logarithmic derivatives of the factors. -/
theorem prodDerivation_prodJet {g : ℕ → Polynomial ℂ} (hg : ∀ j, g j ≠ 0) (k : ℕ) :
    prodDerivation g (prodJet g k) = prodJet g k * logSum g k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hFne : prodFactor g k ≠ 0 := prodFactor_ne_zero hg k
      rw [prodJet_succ, Derivation.leibniz, ih, prodDerivation_prodFactor, logSum_succ]
      simp only [smul_eq_mul]
      have hcancel : prodFactor g k * logFactor g k
          = algebraMap (MvPolynomial ℕ ℂ) CascadeField (univFactor (g k).derivative k) := by
        rw [logFactor]
        field_simp
      calc prodJet g k
              * (algebraMap (MvPolynomial ℕ ℂ) CascadeField (univFactor (g k).derivative k)
                * prodJet g k)
            + prodFactor g k * (prodJet g k * logSum g k)
          = prodJet g k * ((prodFactor g k * logFactor g k) * prodJet g k)
            + prodFactor g k * (prodJet g k * logSum g k) := by
            rw [hcancel]
        _ = prodJet g k * prodFactor g k * (logSum g k + logFactor g k * prodJet g k) := by ring

/-! ## The coordinate derivations -/

/-- The `k`-th coordinate derivation of the rational model. -/
noncomputable def fpderiv (k : ℕ) : Derivation ℂ CascadeField CascadeField :=
  fractionRingDerivation
    (MvPolynomial.mkDerivation ℂ fun j =>
      if j = k then (1 : CascadeField) else 0 :
      Derivation ℂ (MvPolynomial ℕ ℂ) CascadeField)

@[simp] theorem fpderiv_fx_self (k : ℕ) : fpderiv k (fx k) = 1 := by
  rw [fpderiv, fx, fractionRingDerivation_algebraMap, MvPolynomial.mkDerivation_X]
  simp

@[simp] theorem fpderiv_fx_of_ne {j k : ℕ} (h : j ≠ k) : fpderiv k (fx j) = 0 := by
  rw [fpderiv, fx, fractionRingDerivation_algebraMap, MvPolynomial.mkDerivation_X]
  simp [h]

end GaloisForLFunctions.HTGeometry
