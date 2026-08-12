import GaloisForLFunctions.RHTower.RouteEPhysicalSaddleAntiscaleBarrier
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.PrimePhasePortRecurrence
import GaloisForLFunctions.HTGeometry.PrimeEulerProductAperture
import GaloisForLFunctions.RHTower.Sieve.MoebiusSmoothLimit
import GaloisForLFunctions.RHTower.Sieve.DirichletKernelPairing
import GaloisForLFunctions.RHTower.Sieve.SeparatedRowSum
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.RHTower.Sieve.LargeSieveFinite
import GaloisForLFunctions.RHTower.Sieve.OffDiagonalSwap
import GaloisForLFunctions.RHTower.Sieve.LogSeparation

/-!
# Route E critical antiscale dissipation saturation

This module closes the finite-prime critical Euler reporter law.  For

`Psi(Q,r,t) = product_{p in Q} (1 - p^(-r-it)) / (1 + p^(-r))`,

it proves the exact local deficit identity, classifies the all-antiscale point as the unique
modulus-one phase configuration, and uses prime-log recurrence to show that this escape mode is
approached after every height.  Thus pointwise coercivity fails for structural, not perturbative,
reasons.

The complementary finite-height result is also exact.  Squarefree subset products give an
injective frequency expansion with spacing at least the reciprocal primorial.  A general harmonic
Schur estimate for finite separated real-frequency polynomials then yields

`integral_{-W}^{W} |Psi(Q,r,t)|^2 dt
  <= (2 W + 4 R_Q (1 + |Q| log 2)) V(Q,r)`.

The coefficient energy is proved equal to
`V(Q,r) = product_p (1 + p^(-2r)) / (1 + p^(-r))^2`, not merely bounded by it.  Finally,
`V(Q,r) <= exp (-1/2 * sum_p p^(-r))`; hence it tends to zero along every packet family whose
`r`-mass diverges, and in particular along the canonical prime apertures for `0 < r <= 1`.

No route premise, extra logical postulate, numerical computation, or asymptotic placeholder is used.
-/

namespace RHTower

open scoped BigOperators
open HTGeometry.ConstraintMotiveRelativity

noncomputable section

def routeECriticalEulerRadius (r : ℝ) (p : Nat.Primes) : ℝ :=
  ((p : ℕ) : ℝ) ^ (-r)

def routeECriticalEulerLocalDeficit (r : ℝ) (p : Nat.Primes) (t : ℝ) : ℝ :=
  routeECriticalEulerRadius r p *
      Complex.normSq
        (1 + Complex.exp (((t * Real.log (p : ℕ) : ℝ) : ℂ) * Complex.I)) /
    (1 + routeECriticalEulerRadius r p) ^ 2

def routeECriticalEulerFactor (r : ℝ) (p : Nat.Primes) (t : ℝ) : ℂ :=
  (1 - (routeECriticalEulerRadius r p : ℂ) * phaseCovec t p) /
    (1 + routeECriticalEulerRadius r p)

def routeECriticalEulerReporter (Q : Finset Nat.Primes) (r t : ℝ) : ℂ :=
  ∏ p ∈ Q, routeECriticalEulerFactor r p t

def routeECriticalEulerPrimorial (Q : Finset Nat.Primes) : ℕ :=
  ∏ p ∈ Q, (p : ℕ)

def routeECriticalEulerSubsetProduct
    {Q : Finset Nat.Primes} (T : ↥Q.powerset) : ℕ :=
  ∏ p ∈ (T : Finset Nat.Primes), (p : ℕ)

def routeECriticalEulerSubsetFrequency
    {Q : Finset Nat.Primes} (T : ↥Q.powerset) : ℝ :=
  -Real.log (routeECriticalEulerSubsetProduct T : ℝ)

def routeECriticalEulerSelectedCoefficient (r : ℝ) (p : Nat.Primes) : ℂ :=
  ((-(routeECriticalEulerRadius r p / (1 + routeECriticalEulerRadius r p)) : ℝ) : ℂ)

def routeECriticalEulerVacuumCoefficient (r : ℝ) (p : Nat.Primes) : ℂ :=
  (((1 / (1 + routeECriticalEulerRadius r p)) : ℝ) : ℂ)

def routeECriticalEulerSubsetCoefficient
    (Q : Finset Nat.Primes) (r : ℝ) (T : ↥Q.powerset) : ℂ :=
  (∏ p ∈ (T : Finset Nat.Primes), routeECriticalEulerSelectedCoefficient r p) *
    ∏ p ∈ Q \ (T : Finset Nat.Primes), routeECriticalEulerVacuumCoefficient r p

def routeECriticalEulerMeanSquareMass (Q : Finset Nat.Primes) (r : ℝ) : ℝ :=
  ∏ p ∈ Q,
    (1 + routeECriticalEulerRadius r p ^ 2) /
      (1 + routeECriticalEulerRadius r p) ^ 2

def routeECriticalPrimeRadiusMass (N : ℕ) (r : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesBelow N, (p : ℝ) ^ (-r)

def routeECriticalPrimesBelow (N : ℕ) : Finset Nat.Primes :=
  (Nat.primesBelow N).attach.map
    ⟨fun x : {n // n ∈ Nat.primesBelow N} =>
        (⟨x.1, Nat.prime_of_mem_primesBelow x.2⟩ : Nat.Primes),
      fun _ _ h => Subtype.ext (congrArg (fun p : Nat.Primes => p.val) h)⟩

def routeEFiniteFrequencyPolynomial
    (N : ℕ) (lam : ℕ → ℝ) (c : Fin N → ℂ) (t : ℝ) : ℂ :=
  ∑ n : Fin N, c n *
    Complex.exp (((t * lam n : ℝ) : ℂ) * Complex.I)

def routeEFinsetFrequencyPolynomial
    (s : Finset ℝ) (c : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑ x ∈ s, c x * Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)

def routeEFintypeFrequencyPolynomial
    {ι : Type*} [Fintype ι] (lam : ι → ℝ) (c : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ i : ι, c i * Complex.exp (((t * lam i : ℝ) : ℂ) * Complex.I)

theorem routeECriticalEulerRadius_pos {r : ℝ} (p : Nat.Primes) :
    0 < routeECriticalEulerRadius r p := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _

theorem routeECriticalEulerRadius_lt_one {r : ℝ} (hr : 0 < r) (p : Nat.Primes) :
    routeECriticalEulerRadius r p < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (neg_neg_of_pos hr)

theorem routeECriticalEulerPrimorial_pos (Q : Finset Nat.Primes) :
    0 < routeECriticalEulerPrimorial Q := by
  unfold routeECriticalEulerPrimorial
  exact Finset.prod_pos fun p hp => p.2.pos

theorem routeECriticalEulerSubsetProduct_pos
    {Q : Finset Nat.Primes} (T : ↥Q.powerset) :
    0 < routeECriticalEulerSubsetProduct T := by
  unfold routeECriticalEulerSubsetProduct
  exact Finset.prod_pos fun p hp => p.2.pos

theorem routeECriticalEulerSubsetProduct_le_primorial
    {Q : Finset Nat.Primes} (T : ↥Q.powerset) :
    routeECriticalEulerSubsetProduct T ≤ routeECriticalEulerPrimorial Q := by
  unfold routeECriticalEulerSubsetProduct routeECriticalEulerPrimorial
  apply Finset.prod_le_prod_of_subset_of_one_le'
    (Finset.mem_powerset.mp T.property)
  intro p hpQ hpT
  exact p.2.one_lt.le

private theorem routeECriticalEulerSubsetProduct_injective
    (Q : Finset Nat.Primes) :
    Function.Injective
      (fun T : ↥Q.powerset => routeECriticalEulerSubsetProduct T) := by
  classical
  let ePrime : Nat.Primes ↪ ℕ := Function.Embedding.subtype _
  intro S T hST
  apply Subtype.ext
  apply Finset.map_injective ePrime
  apply RHTower.Sieve.prod_injOn_powerset
    (P := Q.map ePrime)
  · intro p hp
    rw [Finset.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact q.2
  · exact Finset.mem_powerset.mpr
      (Finset.map_subset_map.mpr (Finset.mem_powerset.mp S.property))
  · exact Finset.mem_powerset.mpr
      (Finset.map_subset_map.mpr (Finset.mem_powerset.mp T.property))
  · change (∏ p ∈ Finset.map ePrime (S : Finset Nat.Primes), p) =
      ∏ p ∈ Finset.map ePrime (T : Finset Nat.Primes), p
    rw [Finset.prod_map, Finset.prod_map]
    change (∏ p ∈ (S : Finset Nat.Primes), (p : ℕ)) =
      ∏ p ∈ (T : Finset Nat.Primes), (p : ℕ)
    simpa [routeECriticalEulerSubsetProduct] using hST

theorem routeECriticalEulerSubsetFrequency_injective
    (Q : Finset Nat.Primes) :
    Function.Injective
      (fun T : ↥Q.powerset => routeECriticalEulerSubsetFrequency T) := by
  intro S T hST
  apply routeECriticalEulerSubsetProduct_injective Q
  have hlog :
      Real.log (routeECriticalEulerSubsetProduct S : ℝ) =
        Real.log (routeECriticalEulerSubsetProduct T : ℝ) := by
    dsimp [routeECriticalEulerSubsetFrequency] at hST
    linarith
  have hcast : (routeECriticalEulerSubsetProduct S : ℝ) =
      (routeECriticalEulerSubsetProduct T : ℝ) := by
    exact Real.strictMonoOn_log.injOn
      (Set.mem_Ioi.mpr (by exact_mod_cast routeECriticalEulerSubsetProduct_pos S))
      (Set.mem_Ioi.mpr (by exact_mod_cast routeECriticalEulerSubsetProduct_pos T)) hlog
  exact_mod_cast hcast

private theorem one_div_nat_upper_le_abs_log_sub
    {a b R : ℕ} (ha : 0 < a) (hb : 0 < b) (haR : a ≤ R) (hbR : b ≤ R)
    (hab : a ≠ b) :
    1 / (R : ℝ) ≤ |Real.log (a : ℝ) - Real.log (b : ℝ)| := by
  have hR : (0 : ℝ) < (R : ℝ) := by exact_mod_cast lt_of_lt_of_le ha haR
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · have habR : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hablt
    have hgap : (1 : ℝ) ≤ (b : ℝ) - (a : ℝ) := by linarith
    have habLe : (a : ℝ) ≤ (b : ℝ) := by linarith
    have hlog := RHTower.Sieve.log_sub_ge ha' habLe
    have hfrac : 1 / (R : ℝ) ≤ ((b : ℝ) - (a : ℝ)) / (b : ℝ) := by
      rw [div_le_div_iff₀ hR hb']
      have hbR' : (b : ℝ) ≤ (R : ℝ) := by exact_mod_cast hbR
      nlinarith
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log ha' habLe))]
    linarith
  · have hbaR : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hbalt
    have hgap : (1 : ℝ) ≤ (a : ℝ) - (b : ℝ) := by linarith
    have hbaLe : (b : ℝ) ≤ (a : ℝ) := by linarith
    have hlog := RHTower.Sieve.log_sub_ge hb' hbaLe
    have hfrac : 1 / (R : ℝ) ≤ ((a : ℝ) - (b : ℝ)) / (a : ℝ) := by
      rw [div_le_div_iff₀ hR ha']
      have haR' : (a : ℝ) ≤ (R : ℝ) := by exact_mod_cast haR
      nlinarith
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hb' hbaLe))]
    linarith

theorem routeECriticalEulerSubsetFrequency_separated
    (Q : Finset Nat.Primes) (S T : ↥Q.powerset) (hST : S ≠ T) :
    1 / (routeECriticalEulerPrimorial Q : ℝ) ≤
      |routeECriticalEulerSubsetFrequency S -
        routeECriticalEulerSubsetFrequency T| := by
  have hprod : routeECriticalEulerSubsetProduct S ≠
      routeECriticalEulerSubsetProduct T := by
    exact fun h => hST (routeECriticalEulerSubsetProduct_injective Q h)
  have hbase := one_div_nat_upper_le_abs_log_sub
    (routeECriticalEulerSubsetProduct_pos S)
    (routeECriticalEulerSubsetProduct_pos T)
    (routeECriticalEulerSubsetProduct_le_primorial S)
    (routeECriticalEulerSubsetProduct_le_primorial T) hprod
  rw [routeECriticalEulerSubsetFrequency, routeECriticalEulerSubsetFrequency]
  have habs :
      |-Real.log (routeECriticalEulerSubsetProduct S : ℝ) -
          -Real.log (routeECriticalEulerSubsetProduct T : ℝ)| =
        |Real.log (routeECriticalEulerSubsetProduct S : ℝ) -
          Real.log (routeECriticalEulerSubsetProduct T : ℝ)| := by
    rw [show -Real.log (routeECriticalEulerSubsetProduct S : ℝ) -
        -Real.log (routeECriticalEulerSubsetProduct T : ℝ) =
      -(Real.log (routeECriticalEulerSubsetProduct S : ℝ) -
        Real.log (routeECriticalEulerSubsetProduct T : ℝ)) by ring, abs_neg]
  rw [habs]
  exact hbase

theorem routeECriticalEulerSubsetPhase_eq
    {Q : Finset Nat.Primes} (T : ↥Q.powerset) (t : ℝ) :
    (∏ p ∈ (T : Finset Nat.Primes), phaseCovec t p) =
      Complex.exp
        (((t * routeECriticalEulerSubsetFrequency T : ℝ) : ℂ) * Complex.I) := by
  have hlog :
      Real.log (routeECriticalEulerSubsetProduct T : ℝ) =
        ∑ p ∈ (T : Finset Nat.Primes), Real.log (p : ℕ) := by
    rw [routeECriticalEulerSubsetProduct, Nat.cast_prod]
    exact Real.log_prod fun p hp => by exact_mod_cast p.2.pos.ne'
  have hsumReal :
      (∑ p ∈ (T : Finset Nat.Primes), t * Real.log (p : ℕ)) =
        t * Real.log (routeECriticalEulerSubsetProduct T : ℝ) := by
    rw [← Finset.mul_sum, hlog]
  simp_rw [phaseCovec_eq]
  rw [← Complex.exp_sum]
  congr 1
  calc
    ∑ p ∈ (T : Finset Nat.Primes),
        -(Complex.I * (((t * Real.log (p : ℕ) : ℝ)) : ℂ)) =
        -(Complex.I * ∑ p ∈ (T : Finset Nat.Primes),
          (((t * Real.log (p : ℕ) : ℝ)) : ℂ)) := by
            rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
    _ = -(Complex.I *
        (((∑ p ∈ (T : Finset Nat.Primes), t * Real.log (p : ℕ) : ℝ)) : ℂ)) := by
          rw [Complex.ofReal_sum]
    _ = (((t * routeECriticalEulerSubsetFrequency T : ℝ) : ℂ) * Complex.I) := by
      rw [hsumReal, routeECriticalEulerSubsetFrequency]
      simp only [Complex.ofReal_mul, Complex.ofReal_neg]
      ring

theorem routeECriticalEulerFactor_eq_selected_mul_phase_add_vacuum
    (r : ℝ) (p : Nat.Primes) (t : ℝ) :
    routeECriticalEulerFactor r p t =
      routeECriticalEulerSelectedCoefficient r p * phaseCovec t p +
        routeECriticalEulerVacuumCoefficient r p := by
  let u := routeECriticalEulerRadius r p
  have hdenR : (1 + u : ℝ) ≠ 0 := by
    linarith [routeECriticalEulerRadius_pos (r := r) p]
  have hdenC : (1 + (u : ℂ)) ≠ 0 := by exact_mod_cast hdenR
  rw [routeECriticalEulerFactor, routeECriticalEulerSelectedCoefficient,
    routeECriticalEulerVacuumCoefficient]
  change (1 - (u : ℂ) * phaseCovec t p) / (1 + u) =
    ((-(u / (1 + u)) : ℝ) : ℂ) * phaseCovec t p +
      (((1 / (1 + u) : ℝ)) : ℂ)
  push_cast
  field_simp [hdenC]
  ring

theorem routeECriticalEulerReporter_eq_frequencyPolynomial
    (Q : Finset Nat.Primes) (r t : ℝ) :
    routeECriticalEulerReporter Q r t =
      routeEFintypeFrequencyPolynomial
        (fun T : ↥Q.powerset => routeECriticalEulerSubsetFrequency T)
        (routeECriticalEulerSubsetCoefficient Q r) t := by
  classical
  rw [routeECriticalEulerReporter]
  simp_rw [routeECriticalEulerFactor_eq_selected_mul_phase_add_vacuum]
  rw [Finset.prod_add]
  rw [routeEFintypeFrequencyPolynomial]
  rw [← Finset.sum_attach Q.powerset, Finset.attach_eq_univ]
  apply Finset.sum_congr rfl
  intro T hT
  rw [routeECriticalEulerSubsetCoefficient]
  rw [← routeECriticalEulerSubsetPhase_eq T t]
  rw [Finset.prod_mul_distrib]
  ring

@[simp] theorem norm_routeECriticalEulerSelectedCoefficient
    (r : ℝ) (p : Nat.Primes) :
    ‖routeECriticalEulerSelectedCoefficient r p‖ =
      routeECriticalEulerRadius r p / (1 + routeECriticalEulerRadius r p) := by
  rw [routeECriticalEulerSelectedCoefficient, Complex.norm_real, Real.norm_eq_abs,
    abs_neg, abs_of_nonneg]
  exact div_nonneg (routeECriticalEulerRadius_pos (r := r) p).le
    (by linarith [routeECriticalEulerRadius_pos (r := r) p])

@[simp] theorem norm_routeECriticalEulerVacuumCoefficient
    (r : ℝ) (p : Nat.Primes) :
    ‖routeECriticalEulerVacuumCoefficient r p‖ =
      1 / (1 + routeECriticalEulerRadius r p) := by
  rw [routeECriticalEulerVacuumCoefficient, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  exact div_nonneg zero_le_one
    (by linarith [routeECriticalEulerRadius_pos (r := r) p])

theorem normSq_routeECriticalEulerSubsetCoefficient
    (Q : Finset Nat.Primes) (r : ℝ) (T : ↥Q.powerset) :
    ‖routeECriticalEulerSubsetCoefficient Q r T‖ ^ 2 =
      (∏ p ∈ (T : Finset Nat.Primes),
        (routeECriticalEulerRadius r p /
          (1 + routeECriticalEulerRadius r p)) ^ 2) *
      ∏ p ∈ Q \ (T : Finset Nat.Primes),
        (1 / (1 + routeECriticalEulerRadius r p)) ^ 2 := by
  rw [routeECriticalEulerSubsetCoefficient, norm_mul, mul_pow,
    norm_prod, norm_prod, Finset.prod_pow, Finset.prod_pow]
  simp

theorem routeECriticalEulerSubsetCoefficient_energy_eq_mass
    (Q : Finset Nat.Primes) (r : ℝ) :
    (∑ T : ↥Q.powerset, ‖routeECriticalEulerSubsetCoefficient Q r T‖ ^ 2) =
      routeECriticalEulerMeanSquareMass Q r := by
  classical
  simp_rw [normSq_routeECriticalEulerSubsetCoefficient]
  rw [Finset.univ_eq_attach Q.powerset]
  change (∑ T ∈ Q.powerset.attach,
    (fun U : Finset Nat.Primes =>
      (∏ p ∈ U,
        (routeECriticalEulerRadius r p /
          (1 + routeECriticalEulerRadius r p)) ^ 2) *
      ∏ p ∈ Q \ U,
        (1 / (1 + routeECriticalEulerRadius r p)) ^ 2) (T : Finset Nat.Primes)) = _
  have hattach := Finset.sum_attach Q.powerset
    (fun U : Finset Nat.Primes =>
      (∏ p ∈ U,
        (routeECriticalEulerRadius r p /
          (1 + routeECriticalEulerRadius r p)) ^ 2) *
      ∏ p ∈ Q \ U,
        (1 / (1 + routeECriticalEulerRadius r p)) ^ 2)
  rw [hattach]
  rw [← Finset.prod_add]
  rw [routeECriticalEulerMeanSquareMass]
  apply Finset.prod_congr rfl
  intro p hp
  have hden : (1 + routeECriticalEulerRadius r p : ℝ) ≠ 0 := by
    linarith [routeECriticalEulerRadius_pos (r := r) p]
  field_simp [hden]
  ring

@[simp] theorem routeECriticalPrimesBelow_sum_radius
    (N : ℕ) (r : ℝ) :
    (∑ p ∈ routeECriticalPrimesBelow N, routeECriticalEulerRadius r p) =
      routeECriticalPrimeRadiusMass N r := by
  classical
  rw [routeECriticalPrimesBelow, Finset.sum_map]
  simpa [routeECriticalEulerRadius, routeECriticalPrimeRadiusMass] using
    (Finset.sum_attach (Nat.primesBelow N) (fun p : ℕ => (p : ℝ) ^ (-r)))

theorem routeECriticalEulerLocalDeficit_identity
    (r : ℝ) (p : Nat.Primes) (t : ℝ) :
    Complex.normSq (routeECriticalEulerFactor r p t) =
      1 - routeECriticalEulerLocalDeficit r p t := by
  let u := routeECriticalEulerRadius r p
  have hu : u ≠ -1 := by
    have := routeECriticalEulerRadius_pos (r := r) p
    linarith
  have hphase : phaseCovec t p =
      Complex.exp (((-(t * Real.log (p : ℕ)) : ℝ) : ℂ) * Complex.I) := by
    rw [phaseCovec_eq]
    congr 1
    push_cast
    ring
  rw [routeECriticalEulerFactor, routeECriticalEulerLocalDeficit, hphase,
    Complex.normSq_div]
  have hdennorm :
      Complex.normSq (1 + (routeECriticalEulerRadius r p : ℂ)) =
        (1 + routeECriticalEulerRadius r p) ^ 2 := by
    have hcast : (1 : ℂ) + (routeECriticalEulerRadius r p : ℂ) =
        (((1 + routeECriticalEulerRadius r p : ℝ)) : ℂ) := by push_cast; rfl
    rw [hcast]
    rw [Complex.normSq_ofReal]
    ring
  rw [hdennorm]
  exact routeE_eulerFactor_normalized_deficit hu

theorem routeECriticalEulerLocalDeficit_nonneg
    (r : ℝ) (p : Nat.Primes) (t : ℝ) :
    0 ≤ routeECriticalEulerLocalDeficit r p t := by
  unfold routeECriticalEulerLocalDeficit
  exact div_nonneg
    (mul_nonneg (routeECriticalEulerRadius_pos (r := r) p).le
      (Complex.normSq_nonneg _)) (sq_nonneg _)

theorem routeECriticalEulerLocalDeficit_le_one
    (r : ℝ) (p : Nat.Primes) (t : ℝ) :
    routeECriticalEulerLocalDeficit r p t ≤ 1 := by
  let u := routeECriticalEulerRadius r p
  let z := Complex.exp (((t * Real.log (p : ℕ) : ℝ) : ℂ) * Complex.I)
  have hu0 : 0 ≤ u := (routeECriticalEulerRadius_pos (r := r) p).le
  have hnormz : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hnorm : ‖(1 : ℂ) + z‖ ≤ 2 := by
    calc
      ‖(1 : ℂ) + z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_add_le _ _
      _ = 2 := by rw [norm_one, hnormz]; norm_num
  have hsq : Complex.normSq ((1 : ℂ) + z) ≤ 4 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg ((1 : ℂ) + z)]
  have hden : 0 < (1 + u) ^ 2 := sq_pos_of_pos (by linarith [hu0])
  rw [routeECriticalEulerLocalDeficit]
  change u * Complex.normSq ((1 : ℂ) + z) / (1 + u) ^ 2 ≤ 1
  rw [div_le_one hden]
  have hmul : u * Complex.normSq ((1 : ℂ) + z) ≤ 4 * u :=
    by simpa [mul_comm] using mul_le_mul_of_nonneg_left hsq hu0
  nlinarith [sq_nonneg (1 - u)]

theorem routeECriticalEulerLocalDeficit_eq_zero_iff
    (r : ℝ) (p : Nat.Primes) (t : ℝ) :
    routeECriticalEulerLocalDeficit r p t = 0 ↔
      Complex.exp (((t * Real.log (p : ℕ) : ℝ) : ℂ) * Complex.I) = -1 := by
  let u := routeECriticalEulerRadius r p
  let z := Complex.exp (((t * Real.log (p : ℕ) : ℝ) : ℂ) * Complex.I)
  have hu : u ≠ 0 := (routeECriticalEulerRadius_pos (r := r) p).ne'
  have hden : (1 + u) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    linarith [routeECriticalEulerRadius_pos (r := r) p]
  change u * Complex.normSq (1 + z) / (1 + u) ^ 2 = 0 ↔ z = -1
  rw [div_eq_zero_iff, mul_eq_zero, Complex.normSq_eq_zero]
  simp only [hu, false_or]
  constructor
  · rintro (h | hzero)
    · exact eq_neg_of_add_eq_zero_right h
    · exact (hden hzero).elim
  · intro h
    left
    rw [h]
    simp

theorem routeECriticalEulerReporter_normSq_eq_prod_deficit
    (r : ℝ) (Q : Finset Nat.Primes) (t : ℝ) :
    Complex.normSq (routeECriticalEulerReporter Q r t) =
      ∏ p ∈ Q, (1 - routeECriticalEulerLocalDeficit r p t) := by
  rw [routeECriticalEulerReporter, map_prod]
  apply Finset.prod_congr rfl
  intro p hp
  exact routeECriticalEulerLocalDeficit_identity r p t

private theorem prod_one_sub_eq_one_iff
    {ι : Type*} (s : Finset ι) (d : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ d i) (h1 : ∀ i ∈ s, d i ≤ 1) :
    (∏ i ∈ s, (1 - d i)) = 1 ↔ ∀ i ∈ s, d i = 0 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      have ha0 : 0 ≤ 1 - d a := sub_nonneg.mpr (h1 a (Finset.mem_insert_self a s))
      have ha1 : 1 - d a ≤ 1 := by linarith [h0 a (Finset.mem_insert_self a s)]
      have hs0 : 0 ≤ ∏ i ∈ s, (1 - d i) := by
        apply Finset.prod_nonneg
        intro i hi
        exact sub_nonneg.mpr (h1 i (Finset.mem_insert_of_mem hi))
      have hs1 : (∏ i ∈ s, (1 - d i)) ≤ 1 := by
        calc
          (∏ i ∈ s, (1 - d i)) ≤ ∏ _i ∈ s, (1 : ℝ) := by
            apply Finset.prod_le_prod
            · intro i hi
              exact sub_nonneg.mpr (h1 i (Finset.mem_insert_of_mem hi))
            · intro i hi
              linarith [h0 i (Finset.mem_insert_of_mem hi)]
          _ = 1 := by simp
      rw [Finset.prod_insert ha]
      constructor
      · intro hprod
        have hmulA : (1 - d a) * (∏ i ∈ s, (1 - d i)) ≤ 1 - d a := by
          simpa using mul_le_mul_of_nonneg_left hs1 ha0
        have hmulS : (1 - d a) * (∏ i ∈ s, (1 - d i)) ≤
            ∏ i ∈ s, (1 - d i) := by
          simpa using mul_le_mul_of_nonneg_right ha1 hs0
        have hda : d a = 0 := by linarith
        have hsprod : (∏ i ∈ s, (1 - d i)) = 1 := by linarith
        have hsall := (ih
          (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
          (fun i hi => h1 i (Finset.mem_insert_of_mem hi))).mp hsprod
        intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact hda
        · exact hsall i hi
      · intro hall
        have hda := hall a (Finset.mem_insert_self a s)
        have hsall : ∀ i ∈ s, d i = 0 :=
          fun i hi => hall i (Finset.mem_insert_of_mem hi)
        rw [hda, (ih
          (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
          (fun i hi => h1 i (Finset.mem_insert_of_mem hi))).mpr hsall]
        simp

theorem routeECriticalEulerReporter_norm_eq_one_iff_all_antiscale
    (r : ℝ) (Q : Finset Nat.Primes) (t : ℝ) :
    ‖routeECriticalEulerReporter Q r t‖ = 1 ↔
      ∀ p ∈ Q,
        Complex.exp (((t * Real.log (p : ℕ) : ℝ) : ℂ) * Complex.I) = -1 := by
  have hnormSq : Complex.normSq (routeECriticalEulerReporter Q r t) = 1 ↔
      ∀ p ∈ Q, routeECriticalEulerLocalDeficit r p t = 0 := by
    rw [routeECriticalEulerReporter_normSq_eq_prod_deficit]
    exact prod_one_sub_eq_one_iff Q
      (fun p => routeECriticalEulerLocalDeficit r p t)
      (fun p _ => routeECriticalEulerLocalDeficit_nonneg r p t)
      (fun p _ => routeECriticalEulerLocalDeficit_le_one r p t)
  constructor
  · intro hnorm p hp
    apply (routeECriticalEulerLocalDeficit_eq_zero_iff r p t).mp
    have hall := hnormSq.mp (by
      rw [Complex.normSq_eq_norm_sq, hnorm]
      norm_num)
    exact hall p hp
  · intro hphase
    have hsq : Complex.normSq (routeECriticalEulerReporter Q r t) = 1 := by
      apply hnormSq.mpr
      intro p hp
      exact (routeECriticalEulerLocalDeficit_eq_zero_iff r p t).mpr (hphase p hp)
    rw [Complex.normSq_eq_norm_sq] at hsq
    nlinarith [norm_nonneg (routeECriticalEulerReporter Q r t)]

theorem routeECriticalEulerReporter_norm_le_one
    (r : ℝ) (Q : Finset Nat.Primes) (t : ℝ) :
    ‖routeECriticalEulerReporter Q r t‖ ≤ 1 := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1),
    Complex.sq_norm, one_pow,
    routeECriticalEulerReporter_normSq_eq_prod_deficit]
  calc
    ∏ p ∈ Q, (1 - routeECriticalEulerLocalDeficit r p t) ≤
        ∏ _p ∈ Q, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact sub_nonneg.mpr (routeECriticalEulerLocalDeficit_le_one r p t)
      · intro p hp
        linarith [routeECriticalEulerLocalDeficit_nonneg r p t]
    _ = 1 := by simp

theorem exists_gt_phaseCovec_near_antiscale
    (Q : Finset Nat.Primes) (T : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ t : ℝ, T < t ∧ ∀ p : Q, ‖phaseCovec t p + 1‖ < epsilon := by
  classical
  obtain ⟨t0, ht0⟩ := phase_orbit_approx Q (fun _ => Real.pi) (half_pos hepsilon)
  obtain ⟨tau, htau, hreturn⟩ :=
    phase_orbit_recurrent Q (T - t0) (half_pos hepsilon)
  refine ⟨t0 + tau, by linarith, fun p => ?_⟩
  have hadd : phaseCovec (t0 + tau) (p : Nat.Primes) =
      phaseCovec t0 p * phaseCovec tau p := by
    simp only [phaseCovec, portCoef, one_mul]
    exact portPhase_add primeLog t0 tau p
  rw [hadd]
  have htarget : Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I) = -1 :=
    Complex.exp_pi_mul_I
  have hsplit : phaseCovec t0 p * phaseCovec tau p + 1 =
      phaseCovec t0 p * (phaseCovec tau p - 1) + (phaseCovec t0 p + 1) := by ring
  rw [hsplit]
  calc
    ‖phaseCovec t0 p * (phaseCovec tau p - 1) + (phaseCovec t0 p + 1)‖
        ≤ ‖phaseCovec t0 p * (phaseCovec tau p - 1)‖ + ‖phaseCovec t0 p + 1‖ :=
          norm_add_le _ _
    _ = ‖phaseCovec tau p - 1‖ + ‖phaseCovec t0 p - (-1)‖ := by
      rw [norm_mul, norm_phaseCovec, one_mul]
      ring_nf
    _ < epsilon / 2 + epsilon / 2 := add_lt_add (hreturn p) (by simpa [htarget] using ht0 p)
    _ = epsilon := by ring

theorem routeECriticalEulerFactor_sub_one_norm_le_phase
    (r : ℝ) (p : Nat.Primes) (t : ℝ) :
    ‖routeECriticalEulerFactor r p t - 1‖ ≤ ‖phaseCovec t p + 1‖ := by
  let u := routeECriticalEulerRadius r p
  have hu0 : 0 ≤ u := (routeECriticalEulerRadius_pos (r := r) p).le
  have hden : 0 < 1 + u := by linarith
  have hfrac : u / (1 + u) ≤ 1 := (div_le_one hden).2 (by linarith)
  rw [routeECriticalEulerFactor]
  change ‖(1 - (u : ℂ) * phaseCovec t p) / (1 + u) - 1‖ ≤ _
  have heq : (1 - (u : ℂ) * phaseCovec t p) / (1 + u) - 1 =
      -(u / (1 + u) : ℝ) * (phaseCovec t p + 1) := by
    have hdenC : (1 + (u : ℂ)) ≠ 0 := by exact_mod_cast hden.ne'
    have hcast : (((u / (1 + u) : ℝ)) : ℂ) = (u : ℂ) / (1 + (u : ℂ)) := by
      push_cast
      rfl
    rw [hcast]
    field_simp [hdenC]
    ring
  rw [heq, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hu0 hden.le)]
  calc
    u / (1 + u) * ‖phaseCovec t p + 1‖ ≤
        1 * ‖phaseCovec t p + 1‖ :=
      mul_le_mul_of_nonneg_right hfrac (norm_nonneg _)
    _ = ‖phaseCovec t p + 1‖ := one_mul _

theorem exists_gt_routeECriticalEulerReporter_norm_gt_one_sub
    (r : ℝ) (Q : Finset Nat.Primes) (T : ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ t : ℝ, T < t ∧ 1 - epsilon < ‖routeECriticalEulerReporter Q r t‖ := by
  classical
  let delta := epsilon / (2 * (Q.card + 1))
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  obtain ⟨t, ht, hphase⟩ := exists_gt_phaseCovec_near_antiscale Q T hdelta
  refine ⟨t, ht, ?_⟩
  have hfactor : ∀ p ∈ Q, ‖routeECriticalEulerFactor r p t - 1‖ ≤ delta := by
    intro p hp
    exact (routeECriticalEulerFactor_sub_one_norm_le_phase r p t).trans (hphase ⟨p, hp⟩).le
  have hfactorNorm : ∀ p ∈ Q, ‖routeECriticalEulerFactor r p t‖ ≤ 1 := by
    intro p hp
    have hsquare := routeECriticalEulerLocalDeficit_identity r p t
    have hdef := routeECriticalEulerLocalDeficit_nonneg r p t
    rw [Complex.normSq_eq_norm_sq] at hsquare
    have hone : ‖routeECriticalEulerFactor r p t‖ ^ 2 ≤ 1 := by linarith
    nlinarith [norm_nonneg (routeECriticalEulerFactor r p t)]
  have hprod := GaloisForLFunctions.norm_prod_sub_prod_le
    (fun p : Nat.Primes => routeECriticalEulerFactor r p t)
    (fun _ : Nat.Primes => (1 : ℂ)) (le_refl (1 : ℝ)) hdelta.le Q
    hfactorNorm (by simp) hfactor
  simp only [one_pow, mul_one, Finset.prod_const_one] at hprod
  rw [← routeECriticalEulerReporter] at hprod
  have hsmall : (Q.card : ℝ) * delta < epsilon := by
    dsimp [delta]
    have hcard : (0 : ℝ) ≤ Q.card := by positivity
    have hden : (0 : ℝ) < 2 * (Q.card + 1) := by positivity
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hden).2
    nlinarith [hepsilon]
  have hreverse : 1 - ‖routeECriticalEulerReporter Q r t‖ ≤
      ‖routeECriticalEulerReporter Q r t - 1‖ := by
    calc
      1 - ‖routeECriticalEulerReporter Q r t‖ ≤
          ‖(1 : ℂ) - routeECriticalEulerReporter Q r t‖ :=
        by simpa only [norm_one] using
          norm_sub_norm_le (1 : ℂ) (routeECriticalEulerReporter Q r t)
      _ = ‖routeECriticalEulerReporter Q r t - 1‖ := by rw [norm_sub_rev]
  linarith

theorem routeEFiniteFrequencyPolynomial_normSq_eq
    (N : ℕ) (lam : ℕ → ℝ) (c : Fin N → ℂ) (t : ℝ) :
    ((‖routeEFiniteFrequencyPolynomial N lam c t‖ ^ 2 : ℝ) : ℂ) =
      ∑ m : Fin N, ∑ n : Fin N,
        (c m * (starRingEnd ℂ) (c n)) *
          Complex.exp (((t * (lam m - lam n) : ℝ) : ℂ) * Complex.I) := by
  have hz : ((‖routeEFiniteFrequencyPolynomial N lam c t‖ ^ 2 : ℝ) : ℂ) =
      routeEFiniteFrequencyPolynomial N lam c t *
        (starRingEnd ℂ) (routeEFiniteFrequencyPolynomial N lam c t) := by
    rw [RCLike.mul_conj]
    norm_cast
  rw [hz, routeEFiniteFrequencyPolynomial, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul]
  calc
    c m * Complex.exp (((t * lam m : ℝ) : ℂ) * Complex.I) *
          ((starRingEnd ℂ) (c n) *
            (starRingEnd ℂ) (Complex.exp (((t * lam n : ℝ) : ℂ) * Complex.I))) =
        (c m * (starRingEnd ℂ) (c n)) *
          (Complex.exp (((t * lam m : ℝ) : ℂ) * Complex.I) *
            (starRingEnd ℂ) (Complex.exp (((t * lam n : ℝ) : ℂ) * Complex.I))) := by ring
    _ = (c m * (starRingEnd ℂ) (c n)) *
          Complex.exp (((t * (lam m - lam n) : ℝ) : ℂ) * Complex.I) := by
      rw [RHTower.Sieve.exp_phase_mul_conj]

theorem integral_routeEFiniteFrequencyPolynomial_normSq_eq
    (N : ℕ) (lam : ℕ → ℝ) (c : Fin N → ℂ) (W : ℝ) :
    (∫ t in (-W)..W,
        ((‖routeEFiniteFrequencyPolynomial N lam c t‖ ^ 2 : ℝ) : ℂ)) =
      ∑ m : Fin N, ∑ n : Fin N,
        (c m * (starRingEnd ℂ) (c n)) *
          (∫ t in (-W)..W,
            Complex.exp (((t * (lam m - lam n) : ℝ) : ℂ) * Complex.I)) := by
  classical
  rw [intervalIntegral.integral_congr
    (fun t _ => routeEFiniteFrequencyPolynomial_normSq_eq N lam c t)]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun n _ => ?_
      exact intervalIntegral.integral_const_mul _ _
    · exact fun n _ =>
        (RHTower.Sieve.intervalIntegrable_exp_phase (lam m - lam n) (-W) W).const_mul _
  · intro m _
    have hsum := IntervalIntegrable.sum (μ := MeasureTheory.volume) (a := -W) (b := W)
      (Finset.univ : Finset (Fin N))
      (f := fun n t => (c m * (starRingEnd ℂ) (c n)) *
        Complex.exp (((t * (lam m - lam n) : ℝ) : ℂ) * Complex.I))
      (fun n _ =>
        (RHTower.Sieve.intervalIntegrable_exp_phase (lam m - lam n) (-W) W).const_mul _)
    have heq :
        (∑ n : Fin N, fun t : ℝ => (c m * (starRingEnd ℂ) (c n)) *
          Complex.exp (((t * (lam m - lam n) : ℝ) : ℂ) * Complex.I)) =
        fun t : ℝ => ∑ n : Fin N, (c m * (starRingEnd ℂ) (c n)) *
          Complex.exp (((t * (lam m - lam n) : ℝ) : ℂ) * Complex.I) := by
      funext t
      simp [Finset.sum_apply]
    rw [heq] at hsum
    exact hsum

theorem integral_routeEFiniteFrequencyPolynomial_normSq_sub_diag
    (N : ℕ) (lam : ℕ → ℝ) (c : Fin N → ℂ) (W : ℝ) :
    (∫ t in (-W)..W,
        ((‖routeEFiniteFrequencyPolynomial N lam c t‖ ^ 2 : ℝ) : ℂ)) -
          ((2 * W : ℝ) : ℂ) * ∑ m : Fin N, ((‖c m‖ ^ 2 : ℝ) : ℂ) =
      ∑ m : Fin N, ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m,
        (c m * (starRingEnd ℂ) (c n)) *
          (∫ t in (-W)..W,
            Complex.exp (((t * (lam m - lam n) : ℝ) : ℂ) * Complex.I)) := by
  classical
  rw [integral_routeEFiniteFrequencyPolynomial_normSq_eq]
  have hsplit : ∀ m : Fin N,
      (∑ n : Fin N, (c m * (starRingEnd ℂ) (c n)) *
          (∫ t in (-W)..W,
            Complex.exp (((t * (lam m - lam n) : ℝ) : ℂ) * Complex.I))) =
        (c m * (starRingEnd ℂ) (c m)) *
          (∫ t in (-W)..W,
            Complex.exp (((t * (lam m - lam m) : ℝ) : ℂ) * Complex.I)) +
        ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m,
          (c m * (starRingEnd ℂ) (c n)) *
            (∫ t in (-W)..W,
              Complex.exp (((t * (lam m - lam n) : ℝ) : ℂ) * Complex.I)) :=
    fun m => (Finset.add_sum_erase _ _ (Finset.mem_univ m)).symm
  rw [Finset.sum_congr rfl (fun m _ => hsplit m), Finset.sum_add_distrib]
  have hdiag : ∀ m : Fin N,
      (c m * (starRingEnd ℂ) (c m)) *
          (∫ t in (-W)..W,
            Complex.exp (((t * (lam m - lam m) : ℝ) : ℂ) * Complex.I)) =
        ((2 * W : ℝ) : ℂ) * ((‖c m‖ ^ 2 : ℝ) : ℂ) := by
    intro m
    rw [sub_self, RHTower.Sieve.integral_exp_phase_symm_zero,
      RCLike.mul_conj]
    norm_cast
    push_cast
    ac_rfl
  rw [Finset.sum_congr rfl (fun m _ => hdiag m), ← Finset.mul_sum]
  ring

private theorem routeEFiniteFrequency_inv_row_le
    {N : ℕ} {lam : ℕ → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1)) (m : Fin N) :
    ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m,
        1 / |lam n - lam m| ≤
      (2 / delta) * ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) := by
  have hself : (1 : ℝ) / |lam m - lam m| = 0 := by simp
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin N))
    (fun n : Fin N => 1 / |lam n - lam m|) (Finset.mem_univ m)
  rw [hself, zero_add] at hsplit
  have hmrange : (m : ℕ) ∈ Finset.range N := Finset.mem_range.mpr m.isLt
  have hsplitRange := Finset.add_sum_erase (Finset.range N)
    (fun n : ℕ => 1 / |lam n - lam m|) hmrange
  rw [hself, zero_add] at hsplitRange
  calc
    ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m, 1 / |lam n - lam m| =
        ∑ n : Fin N, 1 / |lam n - lam m| := hsplit
    _ = ∑ n ∈ Finset.range N, 1 / |lam n - lam m| :=
      Fin.sum_univ_eq_sum_range (fun n : ℕ => 1 / |lam n - lam m|) N
    _ = ∑ n ∈ (Finset.range N).erase m, 1 / |lam n - lam m| := hsplitRange.symm
    _ ≤ (2 / delta) * ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) :=
      RHTower.Sieve.sum_inv_abs_dist_le hdelta hgap m.isLt

private theorem routeEFiniteFrequency_offDiagonal_le
    {N : ℕ} {lam : ℕ → ℝ} (c : Fin N → ℂ) {delta : ℝ}
    (hdelta : 0 < delta) (hgap : ∀ i, lam i + delta ≤ lam (i + 1)) :
    ∑ m : Fin N, ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m,
        ‖c m‖ * ‖c n‖ * (2 / |lam m - lam n|) ≤
      (4 / delta) * (∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1)) *
        ∑ m : Fin N, ‖c m‖ ^ 2 := by
  classical
  have hterm : ∀ m : Fin N, ∀ n ∈ (Finset.univ : Finset (Fin N)).erase m,
      ‖c m‖ * ‖c n‖ * (2 / |lam m - lam n|) ≤
        ‖c m‖ ^ 2 * (1 / |lam m - lam n|) +
          ‖c n‖ ^ 2 * (1 / |lam m - lam n|) := by
    intro m n hn
    have hab : 2 * ‖c m‖ * ‖c n‖ ≤ ‖c m‖ ^ 2 + ‖c n‖ ^ 2 := by
      nlinarith [sq_nonneg (‖c m‖ - ‖c n‖)]
    have hinv : (0 : ℝ) ≤ 1 / |lam m - lam n| := by positivity
    calc
      ‖c m‖ * ‖c n‖ * (2 / |lam m - lam n|) =
          (2 * ‖c m‖ * ‖c n‖) * (1 / |lam m - lam n|) := by ring
      _ ≤ (‖c m‖ ^ 2 + ‖c n‖ ^ 2) * (1 / |lam m - lam n|) :=
        mul_le_mul_of_nonneg_right hab hinv
      _ = ‖c m‖ ^ 2 * (1 / |lam m - lam n|) +
          ‖c n‖ ^ 2 * (1 / |lam m - lam n|) := by ring
  refine le_trans
    (Finset.sum_le_sum (fun m _ => Finset.sum_le_sum (hterm m))) ?_
  rw [Finset.sum_congr rfl (fun _ _ => Finset.sum_add_distrib),
    Finset.sum_add_distrib]
  let H : ℝ := (2 / delta) * ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1)
  have hfirst :
      ∑ m : Fin N, ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m,
          ‖c m‖ ^ 2 * (1 / |lam m - lam n|) ≤
        H * ∑ m : Fin N, ‖c m‖ ^ 2 := by
    calc
      ∑ m : Fin N, ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m,
          ‖c m‖ ^ 2 * (1 / |lam m - lam n|) =
          ∑ m : Fin N, ‖c m‖ ^ 2 *
            (∑ n ∈ (Finset.univ : Finset (Fin N)).erase m,
              1 / |lam n - lam m|) := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            rw [abs_sub_comm]
      _ ≤ ∑ m : Fin N, ‖c m‖ ^ 2 * H := by
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_left
          (routeEFiniteFrequency_inv_row_le hdelta hgap m) (sq_nonneg _)
      _ = H * ∑ m : Fin N, ‖c m‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        ring
  have hsecond :
      ∑ m : Fin N, ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m,
          ‖c n‖ ^ 2 * (1 / |lam m - lam n|) ≤
        H * ∑ m : Fin N, ‖c m‖ ^ 2 := by
    rw [RHTower.Sieve.sum_erase_swap
      (fun m n : Fin N => ‖c n‖ ^ 2 * (1 / |lam m - lam n|))]
    calc
      ∑ n : Fin N, ∑ m ∈ (Finset.univ : Finset (Fin N)).erase n,
          ‖c n‖ ^ 2 * (1 / |lam m - lam n|) =
          ∑ n : Fin N, ‖c n‖ ^ 2 *
            (∑ m ∈ (Finset.univ : Finset (Fin N)).erase n,
              1 / |lam m - lam n|) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [Finset.mul_sum]
      _ ≤ ∑ n : Fin N, ‖c n‖ ^ 2 * H := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left
          (routeEFiniteFrequency_inv_row_le hdelta hgap n) (sq_nonneg _)
      _ = H * ∑ n : Fin N, ‖c n‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
  dsimp [H] at hfirst hsecond ⊢
  calc
    (∑ m : Fin N, ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m,
        ‖c m‖ ^ 2 * (1 / |lam m - lam n|)) +
        ∑ m : Fin N, ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m,
          ‖c n‖ ^ 2 * (1 / |lam m - lam n|) ≤
      ((2 / delta) * ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1)) *
          ∑ m : Fin N, ‖c m‖ ^ 2 +
        ((2 / delta) * ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1)) *
          ∑ m : Fin N, ‖c m‖ ^ 2 := add_le_add hfirst hsecond
    _ = (4 / delta) * (∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1)) *
        ∑ m : Fin N, ‖c m‖ ^ 2 := by ring

theorem routeEFiniteFrequency_meanValue_error_le
    {N : ℕ} {lam : ℕ → ℝ} (c : Fin N → ℂ) {delta : ℝ}
    (hdelta : 0 < delta) (hgap : ∀ i, lam i + delta ≤ lam (i + 1)) (W : ℝ) :
    ‖(∫ t in (-W)..W,
        ((‖routeEFiniteFrequencyPolynomial N lam c t‖ ^ 2 : ℝ) : ℂ)) -
          ((2 * W : ℝ) : ℂ) * ∑ m : Fin N, ((‖c m‖ ^ 2 : ℝ) : ℂ)‖ ≤
      (4 / delta) * (∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1)) *
        ∑ m : Fin N, ‖c m‖ ^ 2 := by
  classical
  rw [integral_routeEFiniteFrequencyPolynomial_normSq_sub_diag]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun m _ => norm_sum_le _ _)) ?_
  refine le_trans (Finset.sum_le_sum (fun m _ => Finset.sum_le_sum (fun n hn => ?_)))
    (routeEFiniteFrequency_offDiagonal_le c hdelta hgap)
  have hmn : (m : ℕ) ≠ (n : ℕ) := by
    intro h
    exact (Finset.mem_erase.mp hn).1 (Fin.ext h).symm
  have hlam : lam m ≠ lam n := by
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · exact ne_of_lt (RHTower.Sieve.lt_of_gap hdelta hgap hlt)
    · exact ne_of_gt (RHTower.Sieve.lt_of_gap hdelta hgap hgt)
  rw [norm_mul, norm_mul, RCLike.norm_conj]
  exact mul_le_mul_of_nonneg_left
    (RHTower.Sieve.norm_integral_exp_phase_symm_le_inv
      (lam m - lam n) (sub_ne_zero.mpr hlam) W)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem routeEFiniteFrequency_meanValue_le
    {N : ℕ} {lam : ℕ → ℝ} (c : Fin N → ℂ) {delta : ℝ}
    (hdelta : 0 < delta) (hgap : ∀ i, lam i + delta ≤ lam (i + 1)) (W : ℝ) :
    (∫ t in (-W)..W, ‖routeEFiniteFrequencyPolynomial N lam c t‖ ^ 2) ≤
      (2 * W + (4 / delta) * (1 + Real.log N)) *
        ∑ m : Fin N, ‖c m‖ ^ 2 := by
  have hbase := routeEFiniteFrequency_meanValue_error_le c hdelta hgap W
  have hcast :
      (∫ t in (-W)..W,
          ((‖routeEFiniteFrequencyPolynomial N lam c t‖ ^ 2 : ℝ) : ℂ)) -
            ((2 * W : ℝ) : ℂ) * ∑ m : Fin N, ((‖c m‖ ^ 2 : ℝ) : ℂ) =
        (((∫ t in (-W)..W, ‖routeEFiniteFrequencyPolynomial N lam c t‖ ^ 2) -
          2 * W * ∑ m : Fin N, ‖c m‖ ^ 2 : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_ofReal, ← Complex.ofReal_sum,
      ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hbase
  have hharm : ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) ≤ 1 + Real.log N := by
    rw [← RHTower.Sieve.sum_Icc_one_div_eq_sum_range]
    exact RHTower.Sieve.sum_Icc_one_div_le_one_add_log N
  have hcoef : (0 : ℝ) ≤ (4 / delta) * ∑ m : Fin N, ‖c m‖ ^ 2 := by positivity
  have herror :
      (4 / delta) * (∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1)) *
          ∑ m : Fin N, ‖c m‖ ^ 2 ≤
        (4 / delta) * (1 + Real.log N) * ∑ m : Fin N, ‖c m‖ ^ 2 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hharm (by positivity))
      (Finset.sum_nonneg fun m _ => sq_nonneg _)
  have habove :
      (∫ t in (-W)..W, ‖routeEFiniteFrequencyPolynomial N lam c t‖ ^ 2) -
          2 * W * ∑ m : Fin N, ‖c m‖ ^ 2 ≤
        (4 / delta) * (1 + Real.log N) * ∑ m : Fin N, ‖c m‖ ^ 2 :=
    (le_abs_self _).trans (hbase.trans herror)
  linarith

theorem routeEFinsetFrequency_meanValue_le
    (s : Finset ℝ) (c : ℝ → ℂ) {delta : ℝ} (hdelta : 0 < delta)
    (hs : s.Nonempty)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → delta ≤ |x - y|) (W : ℝ) :
    (∫ t in (-W)..W, ‖routeEFinsetFrequencyPolynomial s c t‖ ^ 2) ≤
      (2 * W + (4 / delta) * (1 + Real.log s.card)) *
        ∑ x ∈ s, ‖c x‖ ^ 2 := by
  classical
  obtain ⟨R, hR⟩ : ∃ R, s.card = R + 1 := by
    have hcard : 0 < s.card := Finset.card_pos.mpr hs
    exact ⟨s.card - 1, by omega⟩
  let e : Fin (R + 1) ≃o ↥s := s.orderIsoOfFin hR
  let lam : ℕ → ℝ := fun i => if h : i < R + 1 then ((e ⟨i, h⟩ : s) : ℝ) else 0
  have hlam_eq : ∀ (i : ℕ) (h : i < R + 1), lam i = ((e ⟨i, h⟩ : s) : ℝ) := by
    intro i hi
    dsimp [lam]
    rw [dif_pos hi]
  have hlam_mem : ∀ (i : ℕ) (h : i < R + 1), lam i ∈ s := by
    intro i hi
    rw [hlam_eq i hi]
    exact (e ⟨i, hi⟩).2
  have hgapFinite : ∀ i, i < R → lam i + delta ≤ lam (i + 1) := by
    intro i hi
    have hi : i < R + 1 := by omega
    have his : i + 1 < R + 1 := by omega
    have hlt : lam i < lam (i + 1) := by
      rw [hlam_eq i hi, hlam_eq (i + 1) his]
      exact e.lt_iff_lt.mpr (by simp [Fin.lt_def])
    have hseparate := hsep (lam i) (hlam_mem i hi)
      (lam (i + 1)) (hlam_mem (i + 1) his) (ne_of_lt hlt)
    rw [abs_of_nonpos (by linarith)] at hseparate
    linarith
  let lamExt : ℕ → ℝ := RHTower.Sieve.extendSeq lam R delta
  have hgap : ∀ i, lamExt i + delta ≤ lamExt (i + 1) :=
    RHTower.Sieve.gap_extendSeq hgapFinite
  let cFin : Fin (R + 1) → ℂ := fun i => c ((e i : s) : ℝ)
  have hpoly : ∀ t,
      routeEFiniteFrequencyPolynomial (R + 1) lamExt cFin t =
        routeEFinsetFrequencyPolynomial s c t := by
    intro t
    rw [routeEFiniteFrequencyPolynomial, routeEFinsetFrequencyPolynomial]
    have hleft :
        (∑ i : Fin (R + 1), cFin i *
            Complex.exp (((t * lamExt i : ℝ) : ℂ) * Complex.I)) =
          ∑ i : Fin (R + 1), c (((e i : s) : ℝ)) *
            Complex.exp (((t * ((e i : s) : ℝ) : ℝ) : ℂ) * Complex.I) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hle : (i : ℕ) ≤ R := by omega
      dsimp [lamExt, cFin]
      rw [RHTower.Sieve.extendSeq_of_le hle, hlam_eq i i.isLt]
    rw [hleft]
    have hsum :
        (∑ i : Fin (R + 1), c (((e i : s) : ℝ)) *
            Complex.exp (((t * ((e i : s) : ℝ) : ℝ) : ℂ) * Complex.I)) =
          ∑ x ∈ s, c x * Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) := by
      rw [← Finset.sum_coe_sort s
        (fun x => c x * Complex.exp (((t * x : ℝ) : ℂ) * Complex.I))]
      exact Equiv.sum_comp e.toEquiv
        (fun y : s => c ((y : s) : ℝ) *
          Complex.exp (((t * ((y : s) : ℝ) : ℝ) : ℂ) * Complex.I))
    exact hsum
  have henergy : (∑ i : Fin (R + 1), ‖cFin i‖ ^ 2) =
      ∑ x ∈ s, ‖c x‖ ^ 2 := by
    rw [← Finset.sum_coe_sort s (fun x => ‖c x‖ ^ 2)]
    exact Equiv.sum_comp e.toEquiv (fun y : s => ‖c ((y : s) : ℝ)‖ ^ 2)
  have hbase := routeEFiniteFrequency_meanValue_le cFin hdelta hgap W
  simp_rw [hpoly] at hbase
  rw [henergy, ← hR] at hbase
  exact hbase

theorem routeEFintypeFrequency_meanValue_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (lam : ι → ℝ) (c : ι → ℂ) (hlam : Function.Injective lam)
    {delta : ℝ} (hdelta : 0 < delta)
    (hsep : ∀ i j, i ≠ j → delta ≤ |lam i - lam j|) (W : ℝ) :
    (∫ t in (-W)..W, ‖routeEFintypeFrequencyPolynomial lam c t‖ ^ 2) ≤
      (2 * W + (4 / delta) * (1 + Real.log (Fintype.card ι))) *
        ∑ i : ι, ‖c i‖ ^ 2 := by
  classical
  let s : Finset ℝ := (Finset.univ : Finset ι).image lam
  let cReal : ℝ → ℂ := fun x => c (Function.invFun lam x)
  have hs : s.Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨lam i, by simp [s]⟩
  have hsepReal : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → delta ≤ |x - y| := by
    intro x hx y hy hxy
    change x ∈ (Finset.univ : Finset ι).image lam at hx
    change y ∈ (Finset.univ : Finset ι).image lam at hy
    rw [Finset.mem_image] at hx hy
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, rfl⟩ := hy
    exact hsep i j (fun hij => hxy (congrArg lam hij))
  have hbase := routeEFinsetFrequency_meanValue_le s cReal hdelta hs hsepReal W
  have hpoly : ∀ t,
      routeEFinsetFrequencyPolynomial s cReal t =
        routeEFintypeFrequencyPolynomial lam c t := by
    intro t
    rw [routeEFinsetFrequencyPolynomial, routeEFintypeFrequencyPolynomial]
    change (∑ x ∈ (Finset.univ : Finset ι).image lam,
      cReal x * Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) = _
    rw [Finset.sum_image hlam.injOn]
    apply Finset.sum_congr rfl
    intro i hi
    change c (Function.invFun lam (lam i)) * _ = c i * _
    rw [Function.leftInverse_invFun hlam i]
  have henergy : (∑ x ∈ s, ‖cReal x‖ ^ 2) = ∑ i : ι, ‖c i‖ ^ 2 := by
    change (∑ x ∈ (Finset.univ : Finset ι).image lam, ‖cReal x‖ ^ 2) = _
    rw [Finset.sum_image hlam.injOn]
    apply Finset.sum_congr rfl
    intro i hi
    change ‖c (Function.invFun lam (lam i))‖ ^ 2 = ‖c i‖ ^ 2
    rw [Function.leftInverse_invFun hlam i]
  have hcard : s.card = Fintype.card ι := by
    change ((Finset.univ : Finset ι).image lam).card = Fintype.card ι
    rw [Finset.card_image_of_injective _ hlam, Finset.card_univ]
  simp_rw [hpoly] at hbase
  rw [henergy, hcard] at hbase
  exact hbase

theorem routeECriticalEulerReporter_meanValue_le
    (Q : Finset Nat.Primes) (r W : ℝ) :
    (∫ t in (-W)..W, ‖routeECriticalEulerReporter Q r t‖ ^ 2) ≤
      (2 * W + 4 * (routeECriticalEulerPrimorial Q : ℝ) *
        (1 + (Q.card : ℝ) * Real.log 2)) *
          routeECriticalEulerMeanSquareMass Q r := by
  classical
  let emptySubset : ↥Q.powerset :=
    ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset Q)⟩
  letI : Nonempty ↥Q.powerset := ⟨emptySubset⟩
  let delta : ℝ := 1 / (routeECriticalEulerPrimorial Q : ℝ)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact one_div_pos.mpr (by exact_mod_cast routeECriticalEulerPrimorial_pos Q)
  have hbase := routeEFintypeFrequency_meanValue_le
    (fun T : ↥Q.powerset => routeECriticalEulerSubsetFrequency T)
    (routeECriticalEulerSubsetCoefficient Q r)
    (routeECriticalEulerSubsetFrequency_injective Q) hdelta
    (fun S T hST => routeECriticalEulerSubsetFrequency_separated Q S T hST) W
  have hpoly : ∀ t,
      routeEFintypeFrequencyPolynomial
          (fun T : ↥Q.powerset => routeECriticalEulerSubsetFrequency T)
          (routeECriticalEulerSubsetCoefficient Q r) t =
        routeECriticalEulerReporter Q r t :=
    fun t => (routeECriticalEulerReporter_eq_frequencyPolynomial Q r t).symm
  simp_rw [hpoly] at hbase
  rw [routeECriticalEulerSubsetCoefficient_energy_eq_mass] at hbase
  have hcard : Fintype.card ↥Q.powerset = 2 ^ Q.card := by
    rw [Fintype.card_coe, Finset.card_powerset]
  rw [hcard] at hbase
  have hlogpow : Real.log ((2 ^ Q.card : ℕ) : ℝ) =
      (Q.card : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hprimorialNe : (routeECriticalEulerPrimorial Q : ℝ) ≠ 0 := by
    exact_mod_cast (routeECriticalEulerPrimorial_pos Q).ne'
  dsimp [delta] at hbase
  rw [hlogpow] at hbase
  have hconstant :
      4 / (1 / (routeECriticalEulerPrimorial Q : ℝ)) =
        4 * (routeECriticalEulerPrimorial Q : ℝ) := by
    field_simp [hprimorialNe]
  rw [hconstant] at hbase
  exact hbase

private theorem criticalEulerMass_local_le_exp
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 + u ^ 2) / (1 + u) ^ 2 ≤ Real.exp (-(u / 2)) := by
  have hden : 0 < (1 + u) ^ 2 := sq_pos_of_pos (by linarith)
  have hden_le : (1 + u) ^ 2 ≤ 4 := by nlinarith
  have hfrac : u / 2 ≤ 2 * u / (1 + u) ^ 2 := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hden]
    nlinarith
  have hid : (1 + u ^ 2) / (1 + u) ^ 2 =
      1 - 2 * u / (1 + u) ^ 2 := by
    field_simp [ne_of_gt hden]
    ring
  rw [hid]
  calc
    1 - 2 * u / (1 + u) ^ 2 ≤ 1 - u / 2 := sub_le_sub_left hfrac 1
    _ ≤ Real.exp (-(u / 2)) := Real.one_sub_le_exp_neg (u / 2)

theorem routeECriticalEulerMeanSquareMass_nonneg
    (Q : Finset Nat.Primes) (r : ℝ) :
    0 ≤ routeECriticalEulerMeanSquareMass Q r := by
  classical
  unfold routeECriticalEulerMeanSquareMass
  apply Finset.prod_nonneg
  intro p hp
  exact div_nonneg (by positivity) (sq_nonneg _)

theorem routeECriticalEulerMeanSquareMass_le_exp_neg_half_sum
    (Q : Finset Nat.Primes) {r : ℝ} (hr : 0 < r) :
    routeECriticalEulerMeanSquareMass Q r ≤
      Real.exp (-(1 / 2 : ℝ) * ∑ p ∈ Q, routeECriticalEulerRadius r p) := by
  classical
  rw [routeECriticalEulerMeanSquareMass]
  calc
    (∏ p ∈ Q, (1 + routeECriticalEulerRadius r p ^ 2) /
        (1 + routeECriticalEulerRadius r p) ^ 2) ≤
        ∏ p ∈ Q, Real.exp (-(routeECriticalEulerRadius r p / 2)) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact div_nonneg (by positivity) (sq_nonneg _)
      · intro p hp
        exact criticalEulerMass_local_le_exp
          (routeECriticalEulerRadius_pos (r := r) p).le
          (routeECriticalEulerRadius_lt_one hr p).le
    _ = Real.exp (∑ p ∈ Q, -(routeECriticalEulerRadius r p / 2)) := by
      rw [Real.exp_sum]
    _ = Real.exp (-(1 / 2 : ℝ) * ∑ p ∈ Q, routeECriticalEulerRadius r p) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

theorem tendsto_routeECriticalEulerMeanSquareMass_zero_of_radiusMass
    {Q : ℕ → Finset Nat.Primes} {r : ℝ} (hr : 0 < r)
    (hsum : Filter.Tendsto
      (fun N => ∑ p ∈ Q N, routeECriticalEulerRadius r p)
      Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun N => routeECriticalEulerMeanSquareMass (Q N) r)
      Filter.atTop (nhds 0) := by
  have hhalf : Filter.Tendsto
      (fun N => (1 / 2 : ℝ) *
        ∑ p ∈ Q N, routeECriticalEulerRadius r p)
      Filter.atTop Filter.atTop := hsum.const_mul_atTop (by norm_num)
  have hneg : Filter.Tendsto
      (fun N => -((1 / 2 : ℝ) *
        ∑ p ∈ Q N, routeECriticalEulerRadius r p))
      Filter.atTop Filter.atBot := Filter.tendsto_neg_atTop_atBot.comp hhalf
  have hexp : Filter.Tendsto
      (fun N => Real.exp (-((1 / 2 : ℝ) *
        ∑ p ∈ Q N, routeECriticalEulerRadius r p)))
      Filter.atTop (nhds 0) := Real.tendsto_exp_atBot.comp hneg
  exact squeeze_zero
    (fun N => routeECriticalEulerMeanSquareMass_nonneg _ _)
    (fun N => routeECriticalEulerMeanSquareMass_le_exp_neg_half_sum (Q N) hr)
    (by simpa only [neg_mul] using hexp)

theorem tendsto_routeECriticalPrimeRadiusMass_atTop
    {r : ℝ} (hr1 : r ≤ 1) :
  Filter.Tendsto (fun N => routeECriticalPrimeRadiusMass N r)
      Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_mono' Filter.atTop ?_
    RHTower.Sieve.tendsto_sum_primesBelow_inv_atTop
  filter_upwards [] with N
  rw [routeECriticalPrimeRadiusMass]
  apply Finset.sum_le_sum
  intro p hp
  have hprime := Nat.prime_of_mem_primesBelow hp
  have hbase : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.one_lt.le
  have hpow := Real.rpow_le_rpow_of_exponent_le hbase (by linarith : (-1 : ℝ) ≤ -r)
  simpa [Real.rpow_neg_one, one_div] using hpow

theorem tendsto_routeECriticalEulerApertureMeanSquareMass_zero
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    Filter.Tendsto
      (fun N => routeECriticalEulerMeanSquareMass (routeECriticalPrimesBelow N) r)
      Filter.atTop (nhds 0) := by
  have hsum := tendsto_routeECriticalPrimeRadiusMass_atTop hr1
  apply tendsto_routeECriticalEulerMeanSquareMass_zero_of_radiusMass hr0
  simpa using hsum

end

end RHTower
