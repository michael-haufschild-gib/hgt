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
noncomputable def fact (p : Polynomial ℂ) (j : ℕ) : CascadeField :=
  algebraMap (MvPolynomial ℕ ℂ) CascadeField (univFactor p j)

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

theorem fact_ne_zero {p : Polynomial ℂ} (hp : p ≠ 0) (j : ℕ) :
    fact p j ≠ 0 := by
  rw [fact]
  intro h0
  refine univFactor_ne_zero hp j ?_
  have hinj : Function.Injective
      (algebraMap (MvPolynomial ℕ ℂ) CascadeField) := IsFractionRing.injective _ _
  exact hinj (by rw [h0, map_zero])

/-! ## The product law

The law of a cascade of first-order linear maps has the shape

`δ X_k = (∏_(j<k) Q_j(X_j)) · v_k(X_k)`,

a product of univariate factors over the earlier coordinates, times one univariate factor in the
coordinate itself.  The exponential tower is the case `Q_j = v_k = X`. -/

/-- The jet of the `k`-th coordinate: earlier factors times the terminal factor. -/
noncomputable def prodJet (Q v : ℕ → Polynomial ℂ) (k : ℕ) : CascadeField :=
  (∏ j ∈ Finset.range k, fact (Q j) j) * fact (v k) k

/-- The product of the earlier factors alone. -/
noncomputable def prodHead (Q : ℕ → Polynomial ℂ) (k : ℕ) : CascadeField :=
  ∏ j ∈ Finset.range k, fact (Q j) j

@[simp] theorem prodHead_zero (Q : ℕ → Polynomial ℂ) : prodHead Q 0 = 1 := by
  simp [prodHead]

theorem prodHead_succ (Q : ℕ → Polynomial ℂ) (k : ℕ) :
    prodHead Q (k + 1) = prodHead Q k * fact (Q k) k := by
  rw [prodHead, prodHead, Finset.prod_range_succ]

theorem prodJet_eq (Q v : ℕ → Polynomial ℂ) (k : ℕ) :
    prodJet Q v k = prodHead Q k * fact (v k) k := rfl

theorem prodHead_ne_zero {Q : ℕ → Polynomial ℂ} (hQ : ∀ j, Q j ≠ 0) (k : ℕ) :
    prodHead Q k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => fact_ne_zero (hQ j) j

theorem prodJet_ne_zero {Q v : ℕ → Polynomial ℂ} (hQ : ∀ j, Q j ≠ 0) (hv : ∀ j, v j ≠ 0) (k : ℕ) :
    prodJet Q v k ≠ 0 :=
  mul_ne_zero (prodHead_ne_zero hQ k) (fact_ne_zero (hv k) k)

/-- The product law as a derivation of the polynomial ring into the rational model. -/
noncomputable def prodDerivationPoly (Q v : ℕ → Polynomial ℂ) :
    Derivation ℂ (MvPolynomial ℕ ℂ) CascadeField :=
  MvPolynomial.mkDerivation ℂ fun k => prodJet Q v k

@[simp] theorem prodDerivationPoly_X (Q v : ℕ → Polynomial ℂ) (k : ℕ) :
    prodDerivationPoly Q v (MvPolynomial.X k) = prodJet Q v k :=
  MvPolynomial.mkDerivation_X ℂ _ k

/-- **The product law on the rational model.** -/
noncomputable def prodDerivation (Q v : ℕ → Polynomial ℂ) :
    Derivation ℂ CascadeField CascadeField :=
  fractionRingDerivation (prodDerivationPoly Q v)

@[simp] theorem prodDerivation_fx (Q v : ℕ → Polynomial ℂ) (k : ℕ) :
    prodDerivation Q v (fx k) = prodJet Q v k := by
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
noncomputable def logFactor (p : Polynomial ℂ) (j : ℕ) : CascadeField :=
  fact p.derivative j / fact p j

/-- The logarithmic derivative of the earlier factors, weighted by the coordinate jets. -/
noncomputable def logSum (Q v : ℕ → Polynomial ℂ) (k : ℕ) : CascadeField :=
  ∑ j ∈ Finset.range k, logFactor (Q j) j * prodJet Q v j

@[simp] theorem logSum_zero (Q v : ℕ → Polynomial ℂ) : logSum Q v 0 = 0 := by
  simp [logSum]

theorem logSum_succ (Q v : ℕ → Polynomial ℂ) (k : ℕ) :
    logSum Q v (k + 1) = logSum Q v k + logFactor (Q k) k * prodJet Q v k := by
  rw [logSum, logSum, Finset.sum_range_succ]

/-- The derivation of a single factor. -/
theorem prodDerivation_fact (Q v : ℕ → Polynomial ℂ) (p : Polynomial ℂ) (k : ℕ) :
    prodDerivation Q v (fact p k) = fact p.derivative k * prodJet Q v k := by
  rw [fact, prodDerivation, fractionRingDerivation_algebraMap,
    derivation_univFactor (prodDerivationPoly Q v) p k, prodDerivationPoly_X,
    Algebra.smul_def]
  rfl

/-- **The logarithmic law of the head product.** -/
theorem prodDerivation_prodHead {Q v : ℕ → Polynomial ℂ} (hQ : ∀ j, Q j ≠ 0) (k : ℕ) :
    prodDerivation Q v (prodHead Q k) = prodHead Q k * logSum Q v k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hFne : fact (Q k) k ≠ 0 := fact_ne_zero (hQ k) k
      rw [prodHead_succ, Derivation.leibniz, ih, prodDerivation_fact, logSum_succ]
      simp only [smul_eq_mul]
      have hcancel : fact (Q k) k * logFactor (Q k) k = fact (Q k).derivative k := by
        rw [logFactor]
        field_simp
      calc prodHead Q k * (fact (Q k).derivative k * prodJet Q v k)
            + fact (Q k) k * (prodHead Q k * logSum Q v k)
          = prodHead Q k * ((fact (Q k) k * logFactor (Q k) k) * prodJet Q v k)
            + fact (Q k) k * (prodHead Q k * logSum Q v k) := by rw [hcancel]
        _ = prodHead Q k * fact (Q k) k
              * (logSum Q v k + logFactor (Q k) k * prodJet Q v k) := by ring

/-- **The logarithmic law of the coordinate jet.**  The extra terminal factor contributes its own
logarithmic derivative, weighted by the jet itself. -/
theorem prodDerivation_prodJet {Q v : ℕ → Polynomial ℂ} (hQ : ∀ j, Q j ≠ 0) (k : ℕ) :
    prodDerivation Q v (prodJet Q v k)
      = prodJet Q v k * (logSum Q v k + logFactor (v k) k * prodJet Q v k) := by
  rcases eq_or_ne (fact (v k) k) 0 with hzero | hne
  · have hjet : prodJet Q v k = 0 := by rw [prodJet_eq, hzero, mul_zero]
    rw [hjet, map_zero, zero_mul]
  · rw [prodJet_eq, Derivation.leibniz, prodDerivation_prodHead hQ,
      prodDerivation_fact]
    simp only [smul_eq_mul]
    have hcancel : fact (v k) k * logFactor (v k) k = fact (v k).derivative k := by
      rw [logFactor]
      field_simp
    calc prodHead Q k * (fact (v k).derivative k * prodJet Q v k)
          + fact (v k) k * (prodHead Q k * logSum Q v k)
        = prodHead Q k * ((fact (v k) k * logFactor (v k) k) * prodJet Q v k)
          + fact (v k) k * (prodHead Q k * logSum Q v k) := by rw [hcancel]
      _ = (prodHead Q k * fact (v k) k)
            * (logSum Q v k + logFactor (v k) k * prodJet Q v k) := by ring
      _ = prodJet Q v k * (logSum Q v k + logFactor (v k) k * prodJet Q v k) := by
          rw [prodJet_eq]

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
