import GaloisForLFunctions.RHTower.GammaCoorientedPositiveConeNoShorting
import GaloisForLFunctions.Hurwitz.ExpIndependence

/-!
# Signed finite Gamma-orbit no-shorting

Positive coorientation excludes nonnegative Gamma shorting but leaves signed
cross-pair incidence open.  This module closes the entire finitely supported,
displacement-independent signed class.

Canonical cross-prime depth edges are oriented by their ordinary primes.
Their modular frequency is

`log (p^(e+1) * q^(f+1))`.

Unique factorization makes this frequency injective.  The actual cooriented
Gamma exterior is the restriction of a nonzero amplitude times the entire
function `sinh (frequency * z)`.  Distinct positive sinh frequencies are
linearly independent by splitting them into the distinct exponential
frequencies `+frequency` and `-frequency` and invoking Vandermonde
independence.  Consequently an orbit-universal finitely supported signed
source chain is zero coefficientwise.

Thus a Route-R null-homotopy cannot be finite and fixed across modular
displacement.  Any survivor must cancel only after an infinite completion or
couple its coefficients nonseparably to divisor provenance.

No Xi zero, zero-location premise, positivity assumption, computation, or
Riemann-hypothesis premise occurs.
-/

open Complex Function Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

def XiGammaEulerCanonicalCrossPrimeDepthPair : Type :=
  {ij : (Nat.Primes × ℕ) × (Nat.Primes × ℕ) //
    (ij.1.1 : ℕ) < (ij.2.1 : ℕ)}

def xiGammaEulerCanonicalCrossPrimePairNat
    (ij : XiGammaEulerCanonicalCrossPrimeDepthPair) : ℕ :=
  xiGammaEulerValuationNat ij.1.1 * xiGammaEulerValuationNat ij.1.2

theorem xiGammaEulerCanonicalCrossPrimePairNat_injective :
    Function.Injective xiGammaEulerCanonicalCrossPrimePairNat := by
  rintro ⟨⟨⟨p, e⟩, ⟨q, f⟩⟩, hpq⟩ ⟨⟨⟨r, g⟩, ⟨s, h⟩⟩, hrs⟩ heq
  change (p : ℕ) ^ (e + 1) * (q : ℕ) ^ (f + 1) =
    (r : ℕ) ^ (g + 1) * (s : ℕ) ^ (h + 1) at heq
  have hpdiv : (p : ℕ) ∣
      (r : ℕ) ^ (g + 1) * (s : ℕ) ^ (h + 1) := by
    rw [← heq]
    exact dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.succ_ne_zero e)) _
  have hqdiv : (q : ℕ) ∣
      (r : ℕ) ^ (g + 1) * (s : ℕ) ^ (h + 1) := by
    rw [← heq]
    exact dvd_mul_of_dvd_right (dvd_pow_self _ (Nat.succ_ne_zero f)) _
  have hpCases : p = r ∨ p = s := by
    rcases p.2.dvd_mul.mp hpdiv with hpr | hps
    · left
      apply Subtype.ext
      exact Nat.prime_eq_prime_of_dvd_pow p.2 r.2 hpr
    · right
      apply Subtype.ext
      exact Nat.prime_eq_prime_of_dvd_pow p.2 s.2 hps
  have hqCases : q = r ∨ q = s := by
    rcases q.2.dvd_mul.mp hqdiv with hqr | hqs
    · left
      apply Subtype.ext
      exact Nat.prime_eq_prime_of_dvd_pow q.2 r.2 hqr
    · right
      apply Subtype.ext
      exact Nat.prime_eq_prime_of_dvd_pow q.2 s.2 hqs
  have hpr : p = r := by
    rcases hpCases with hpr | hps
    · exact hpr
    · rcases hqCases with hqr | hqs
      · have : (s : ℕ) < (r : ℕ) := by simpa [hps, hqr] using hpq
        exact False.elim ((Nat.not_lt_of_ge (Nat.le_of_lt hrs)) this)
      · have : p = q := hps.trans hqs.symm
        exact False.elim ((Nat.ne_of_lt hpq) (congrArg Subtype.val this))
  have hqs : q = s := by
    rcases hqCases with hqr | hqs
    · have : (q : ℕ) = (p : ℕ) := by simpa [hpr] using congrArg Subtype.val hqr
      exact False.elim ((Nat.ne_of_gt hpq) this)
    · exact hqs
  subst r
  subst s
  have hpq_ne : (p : ℕ) ≠ (q : ℕ) := Nat.ne_of_lt hpq
  have he : e = g := by
    have hfac := congrArg (fun n : ℕ => n.factorization (p : ℕ)) heq
    rw [Nat.factorization_mul
        (pow_ne_zero _ p.2.ne_zero) (pow_ne_zero _ q.2.ne_zero),
      Nat.factorization_mul
        (pow_ne_zero _ p.2.ne_zero) (pow_ne_zero _ q.2.ne_zero),
      p.2.factorization_pow, q.2.factorization_pow,
      p.2.factorization_pow, q.2.factorization_pow] at hfac
    simp [hpq_ne] at hfac
    omega
  have hf : f = h := by
    have hfac := congrArg (fun n : ℕ => n.factorization (q : ℕ)) heq
    rw [Nat.factorization_mul
        (pow_ne_zero _ p.2.ne_zero) (pow_ne_zero _ q.2.ne_zero),
      Nat.factorization_mul
        (pow_ne_zero _ p.2.ne_zero) (pow_ne_zero _ q.2.ne_zero),
      p.2.factorization_pow, q.2.factorization_pow,
      p.2.factorization_pow, q.2.factorization_pow] at hfac
    simp [hpq_ne] at hfac
    omega
  subst g
  subst h
  rfl

def xiGammaEulerCanonicalCrossPrimeFrequency
    (ij : XiGammaEulerCanonicalCrossPrimeDepthPair) : ℝ :=
  Real.log (xiGammaEulerCanonicalCrossPrimePairNat ij : ℝ)

theorem xiGammaEulerCanonicalCrossPrimeFrequency_pos
    (ij : XiGammaEulerCanonicalCrossPrimeDepthPair) :
    0 < xiGammaEulerCanonicalCrossPrimeFrequency ij := by
  apply Real.log_pos
  unfold xiGammaEulerCanonicalCrossPrimePairNat xiGammaEulerValuationNat
  have hp : 2 ≤ (ij.1.1.1 : ℕ) := ij.1.1.1.2.two_le
  have hpe : 2 ≤ (ij.1.1.1 : ℕ) ^ (ij.1.1.2 + 1) :=
    le_trans hp (Nat.le_pow (by omega))
  exact_mod_cast lt_of_lt_of_le (show 1 < 2 by omega)
    (le_trans hpe (Nat.le_mul_of_pos_right _
      (pow_pos ij.1.2.1.2.pos _)))

theorem xiGammaEulerCanonicalCrossPrimeFrequency_injective :
    Function.Injective xiGammaEulerCanonicalCrossPrimeFrequency := by
  intro i j h
  apply xiGammaEulerCanonicalCrossPrimePairNat_injective
  apply Nat.cast_injective (R := ℝ)
  apply Real.strictMonoOn_log.injOn
    (Set.mem_Ioi.mpr (Nat.cast_pos.mpr ?_))
    (Set.mem_Ioi.mpr (Nat.cast_pos.mpr ?_))
  · exact h
  · unfold xiGammaEulerCanonicalCrossPrimePairNat xiGammaEulerValuationNat
    exact mul_pos (pow_pos i.1.1.1.2.pos _) (pow_pos i.1.2.1.2.pos _)
  · unfold xiGammaEulerCanonicalCrossPrimePairNat xiGammaEulerValuationNat
    exact mul_pos (pow_pos j.1.1.1.2.pos _) (pow_pos j.1.2.1.2.pos _)

theorem xiGammaEulerCanonicalCrossPrimeFrequency_eq_neg_rate_sum
    (ij : XiGammaEulerCanonicalCrossPrimeDepthPair) :
    xiGammaEulerCanonicalCrossPrimeFrequency ij =
      -(xiGammaEulerPrimitiveModularRate ij.1.1 +
        xiGammaEulerPrimitiveModularRate ij.1.2) := by
  rw [xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight,
    xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight,
    xiGammaEulerBoundaryHalfHeight_eq_half_log_valuation,
    xiGammaEulerBoundaryHalfHeight_eq_half_log_valuation]
  unfold xiGammaEulerCanonicalCrossPrimeFrequency
  rw [xiGammaEulerCanonicalCrossPrimePairNat, Nat.cast_mul]
  have hi : (xiGammaEulerValuationNat ij.1.1 : ℝ) ≠ 0 := by
    exact_mod_cast pow_ne_zero _ ij.1.1.1.2.ne_zero
  have hj : (xiGammaEulerValuationNat ij.1.2 : ℝ) ≠ 0 := by
    exact_mod_cast pow_ne_zero _ ij.1.2.1.2.ne_zero
  rw [Real.log_mul hi hj]
  ring

def xiGammaEulerCanonicalCrossPrimeCoorientedAmplitude
    (ij : XiGammaEulerCanonicalCrossPrimeDepthPair) : ℝ :=
  xiGammaEulerPrimitiveBoundaryAmplitude 0 ij.1.1 *
      xiGammaEulerPrimitiveBoundaryAmplitude 0 ij.1.2 *
      (xiGammaEulerBoundaryHalfHeight ij.1.1.1 ij.1.1.2 -
        xiGammaEulerBoundaryHalfHeight ij.1.2.1 ij.1.2.2) ^ 2

theorem xiGammaEulerCanonicalCrossPrimeCoorientedAmplitude_pos
    (ij : XiGammaEulerCanonicalCrossPrimeDepthPair) :
    0 < xiGammaEulerCanonicalCrossPrimeCoorientedAmplitude ij := by
  have hcells : ij.1.1 ≠ ij.1.2 := by
    intro h
    have hp := congrArg (fun x : Nat.Primes × ℕ => (x.1 : ℕ)) h
    exact (Nat.ne_of_lt ij.2) hp
  have hheight :
      xiGammaEulerBoundaryHalfHeight ij.1.1.1 ij.1.1.2 ≠
        xiGammaEulerBoundaryHalfHeight ij.1.2.1 ij.1.2.2 := by
    intro h
    exact hcells
      (PrimitivePromotedCellHodgeRigidity.xiGammaEulerBoundaryHalfHeight_cell_injective h)
  exact mul_pos
    (mul_pos (xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 ij.1.1)
      (xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 ij.1.2))
    (sq_pos_of_ne_zero (sub_ne_zero.mpr hheight))

def xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit
    (ij : XiGammaEulerCanonicalCrossPrimeDepthPair) (z : ℂ) : ℂ :=
  (xiGammaEulerCanonicalCrossPrimeCoorientedAmplitude ij : ℂ) *
    Complex.sinh ((xiGammaEulerCanonicalCrossPrimeFrequency ij : ℂ) * z)

theorem xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit_ofReal
    (ij : XiGammaEulerCanonicalCrossPrimeDepthPair) (a : ℝ) :
    xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit ij a =
      (xiGammaEulerPrimitiveCoorientedReflectionOddExterior
        a ij.1.1 ij.1.2 : ℂ) := by
  have hreal :
      xiGammaEulerPrimitiveBoundaryAmplitude 0 ij.1.1 *
          xiGammaEulerPrimitiveBoundaryAmplitude 0 ij.1.2 *
          (xiGammaEulerBoundaryHalfHeight ij.1.1.1 ij.1.1.2 -
            xiGammaEulerBoundaryHalfHeight ij.1.2.1 ij.1.2.2) ^ 2 *
          Real.sinh (xiGammaEulerCanonicalCrossPrimeFrequency ij * a) =
        xiGammaEulerPrimitiveCoorientedReflectionOddExterior
          a ij.1.1 ij.1.2 := by
    rw [xiGammaEulerPrimitiveCoorientedReflectionOddExterior,
      xiGammaEulerPrimitiveReflectionOddExterior_eq_sinh,
      xiGammaEulerCanonicalCrossPrimeFrequency_eq_neg_rate_sum]
    rw [show -(xiGammaEulerPrimitiveModularRate ij.1.1 +
        xiGammaEulerPrimitiveModularRate ij.1.2) * a =
        -(a * (xiGammaEulerPrimitiveModularRate ij.1.1 +
          xiGammaEulerPrimitiveModularRate ij.1.2)) by ring,
      Real.sinh_neg]
    ring
  rw [xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit]
  calc
    (xiGammaEulerCanonicalCrossPrimeCoorientedAmplitude ij : ℂ) *
        Complex.sinh
          ((xiGammaEulerCanonicalCrossPrimeFrequency ij : ℂ) * a) =
      (xiGammaEulerPrimitiveBoundaryAmplitude 0 ij.1.1 *
          xiGammaEulerPrimitiveBoundaryAmplitude 0 ij.1.2 *
          (xiGammaEulerBoundaryHalfHeight ij.1.1.1 ij.1.1.2 -
            xiGammaEulerBoundaryHalfHeight ij.1.2.1 ij.1.2.2) ^ 2 *
          Real.sinh (xiGammaEulerCanonicalCrossPrimeFrequency ij * a) : ℝ) := by
            rw [xiGammaEulerCanonicalCrossPrimeCoorientedAmplitude]
            conv_lhs => rhs
                        rw [← Complex.ofReal_mul, ← Complex.ofReal_sinh]
            push_cast
            rfl
    _ = (xiGammaEulerPrimitiveCoorientedReflectionOddExterior
          a ij.1.1 ij.1.2 : ℂ) := congrArg Complex.ofReal hreal

theorem complexExpLin_linearIndependent_fintype
    {ι : Type*} [Fintype ι] {β : ι → ℂ} (hβ : Function.Injective β) :
    LinearIndependent ℂ (fun k : ι => fun z : ℂ => Complex.exp (β k * z)) := by
  let e := Fintype.equivFin ι
  have hfin := HurwitzExp.expLin_linearIndependent
    (β := fun k : Fin (Fintype.card ι) => β (e.symm k))
    (hβ.comp e.symm.injective)
  have hcomp := hfin.comp e e.injective
  simpa [Function.comp_def] using hcomp

theorem complexSinh_realFrequency_linearIndependent_fin
    {n : ℕ} {lam : Fin n → ℝ}
    (hlam : Function.Injective lam) (hpos : ∀ k, 0 < lam k) :
    LinearIndependent ℂ
      (fun k : Fin n => fun z : ℂ => Complex.sinh ((lam k : ℂ) * z)) := by
  let beta : Sum (Fin n) (Fin n) → ℂ :=
    Sum.elim (fun k => (lam k : ℂ)) (fun k => -(lam k : ℂ))
  have hbeta : Function.Injective beta := by
    intro i j hij
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            apply congrArg Sum.inl
            apply hlam
            exact Complex.ofReal_injective hij
        | inr j =>
            exfalso
            change (lam i : ℂ) = -(lam j : ℂ) at hij
            have hreal : lam i = -lam j := Complex.ofReal_injective (by simpa using hij)
            linarith [hpos i, hpos j]
    | inr i =>
        cases j with
        | inl j =>
            exfalso
            change -(lam i : ℂ) = (lam j : ℂ) at hij
            have hreal : -lam i = lam j := Complex.ofReal_injective (by simpa using hij)
            linarith [hpos i, hpos j]
        | inr j =>
            apply congrArg Sum.inr
            apply hlam
            change -(lam i : ℂ) = -(lam j : ℂ) at hij
            exact Complex.ofReal_injective (neg_injective hij)
  have hExp := complexExpLin_linearIndependent_fintype hbeta
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let d : Sum (Fin n) (Fin n) → ℂ :=
    Sum.elim (fun k => c k / 2) (fun k => -(c k / 2))
  have hd_sum :
      (∑ s : Sum (Fin n) (Fin n),
        d s • (fun z : ℂ => Complex.exp (beta s * z))) = 0 := by
    funext z
    have hcz := congrFun hc z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at hcz ⊢
    simp only [Fintype.sum_sum_type, d, beta, Sum.elim_inl, Sum.elim_inr]
    simp only [Complex.sinh] at hcz
    rw [← Finset.sum_add_distrib]
    rw [← hcz]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_comm (lam k : ℂ) z]
    ring
  have hd : d = 0 := by
    rw [Fintype.linearIndependent_iff] at hExp
    funext s
    exact hExp d hd_sum s
  intro k
  have hk := congrFun hd (Sum.inl k)
  simp [d] at hk
  exact hk

theorem complexSinh_realFrequency_linearIndependent
    {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : Function.Injective lam) (hpos : ∀ k, 0 < lam k) :
    LinearIndependent ℂ
      (fun k : ι => fun z : ℂ => Complex.sinh ((lam k : ℂ) * z)) := by
  let e := Fintype.equivFin ι
  have hfin := complexSinh_realFrequency_linearIndependent_fin
    (lam := fun k : Fin (Fintype.card ι) => lam (e.symm k))
    (hlam.comp e.symm.injective) (fun k => hpos (e.symm k))
  have hcomp := hfin.comp e e.injective
  simpa [Function.comp_def] using hcomp

/-- A finite packet of distinct canonical cross-prime depth edges has no
nontrivial displacement-independent signed relation along the complete
complex modular orbit. -/
theorem xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit_linearIndependent
    {ι : Type*} [Fintype ι]
    (edge : ι → XiGammaEulerCanonicalCrossPrimeDepthPair)
    (hedge : Function.Injective edge) :
    LinearIndependent ℂ
      (fun k : ι =>
        xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit (edge k)) := by
  have hfreq : Function.Injective
      (fun k : ι => xiGammaEulerCanonicalCrossPrimeFrequency (edge k)) :=
    xiGammaEulerCanonicalCrossPrimeFrequency_injective.comp hedge
  have hsinh := complexSinh_realFrequency_linearIndependent hfreq
    (fun k => xiGammaEulerCanonicalCrossPrimeFrequency_pos (edge k))
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let d : ι → ℂ := fun k =>
    c k * xiGammaEulerCanonicalCrossPrimeCoorientedAmplitude (edge k)
  have hd_sum :
      (∑ k : ι, d k •
        (fun z : ℂ => Complex.sinh
          ((xiGammaEulerCanonicalCrossPrimeFrequency (edge k) : ℂ) * z))) = 0 := by
    funext z
    have hcz := congrFun hc z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at hcz ⊢
    rw [← hcz]
    apply Finset.sum_congr rfl
    intro k hk
    simp [d, xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit]
    ring
  have hd : d = 0 := by
    rw [Fintype.linearIndependent_iff] at hsinh
    funext k
    exact hsinh d hd_sum k
  intro k
  have hk := congrFun hd k
  simp only [d, Pi.zero_apply] at hk
  exact (mul_eq_zero.mp hk).resolve_right
    (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (xiGammaEulerCanonicalCrossPrimeCoorientedAmplitude_pos (edge k))))

/-- **Signed finite-orbit no-shorting.**  Every finitely supported canonical
cross-prime depth chain is coefficientwise trivial if its fixed signed
weights annihilate the complete modular orbit. -/
theorem xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit_global_linearIndependent :
    LinearIndependent ℂ
      xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro S
  exact xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit_linearIndependent
    (fun ij : S => ij.1) Subtype.val_injective

/-- Explicit finitely supported no-shorting form: an orbit-universal signed
chain has no nonzero coefficient. -/
theorem xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit_finsupp_noShorting
    (c : XiGammaEulerCanonicalCrossPrimeDepthPair →₀ ℂ)
    (h : ∀ z : ℂ, c.sum (fun ij a =>
      a * xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit ij z) = 0) :
    c = 0 := by
  have hLI :=
    xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit_global_linearIndependent
  rw [linearIndependent_iff] at hLI
  apply hLI c
  rw [Finsupp.linearCombination_apply]
  funext z
  simpa [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h z

end

end RHTower
