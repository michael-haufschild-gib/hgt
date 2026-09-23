import GaloisForLFunctions.RHTower.MobiusFiniteSchurTransfer
import GaloisForLFunctions.RHTower.FiniteExponentialPencilMeanSquare
import GaloisForLFunctions.RHTower.PrimeWordSynchronizedCluster
import GaloisForLFunctions.RHTower.PrimeQuadraticGelfondSchneiderPhase

/-!
# The finite prime Möbius transfer is a quantum Loschmidt amplitude

On imaginary integer time, the existing normalized signed prime transfer has the exact form

`L_S(I n) = sum_(T subset S) (-1)^|T| P_sigma(T) exp(-I n log product(T))`.

Thus it is a finite Loschmidt amplitude on the squarefree energy levels `log product(T)`.  Unique
factorization distinguishes the products, while the in-tree Gelfond--Schneider theorem distinguishes
their time-one unitary phases.  The existing finite exponential-pencil mean-square law therefore
identifies the long-time Loschmidt echo with the collision probability, or equivalently the purity
of the dephased squarefree Bernoulli state:

`Cesaro_n |L_S(I n)|^(2 : ℕ) -> sum_T P_sigma(T)^(2 : ℕ) > 0`.

The physics identity is standard finite-spectrum quantum dynamics; see G. Styliaris, N. Anand,
L. Campos Venuti, and P. Zanardi, *Quantum coherence and the localization transition*, Phys. Rev. B
100 (2019), 224204, DOI `10.1103/PhysRevB.100.224204`, Appendix C.  The contribution here is its
exact application to the corpus's prime Möbius/coisometric source.  This is a `[BRIDGE]`, not an RH
proof and not a cofinal-in-aperture lower bound.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The unitary time-one mode of the squarefree energy level indexed by `T`. -/
def finitePrimeSquarefreeLoschmidtMode (T : Finset Nat.Primes) : ℂ :=
  Complex.exp
    (-((Real.log (∏ p ∈ T, (p : ℕ)) : ℝ) : ℂ) * Complex.I)

/-- Every finite squarefree prime product is positive, including the empty product. -/
lemma finitePrimeSquarefreeProduct_pos (T : Finset Nat.Primes) :
    0 < ∏ p ∈ T, (p : ℕ) := by
  exact Finset.prod_pos fun p _ => p.2.pos

/-- Every squarefree Loschmidt mode lies on the unit circle. -/
lemma finitePrimeSquarefreeLoschmidtMode_norm (T : Finset Nat.Primes) :
    ‖finitePrimeSquarefreeLoschmidtMode T‖ = 1 := by
  rw [finitePrimeSquarefreeLoschmidtMode, Complex.norm_exp]
  simp

/-- The mode of a squarefree energy is the product of its one-prime modes. -/
lemma finitePrimeSquarefreeLoschmidtMode_eq_prod (T : Finset Nat.Primes) :
    finitePrimeSquarefreeLoschmidtMode T =
      ∏ p ∈ T, Complex.exp (-((Real.log (p : ℕ) : ℝ) : ℂ) * Complex.I) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [finitePrimeSquarefreeLoschmidtMode]
  | @insert p T hp ih =>
      rw [finitePrimeSquarefreeLoschmidtMode]
      simp only [Finset.prod_insert hp]
      have hpR : (((p : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast p.2.ne_zero
      have hTR : (∏ q ∈ T, (((q : ℕ) : ℝ))) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun q _ => by exact_mod_cast q.2.ne_zero
      rw [Real.log_mul hpR hTR]
      rw [Complex.ofReal_add]
      rw [show -((Real.log (p : ℕ) : ℂ) +
          (Real.log (∏ q ∈ T, (q : ℕ)) : ℂ)) * I =
          -((Real.log (p : ℕ) : ℂ)) * I +
            -((Real.log (∏ q ∈ T, (q : ℕ)) : ℂ)) * I by ring]
      rw [Complex.exp_add, ← finitePrimeSquarefreeLoschmidtMode]
      rw [ih]

/-- A nontrivial positive rational base cannot have unit principal `I`-power.  This is the exact
Gelfond--Schneider phase-separation lemma consumed by the squarefree spectrum. -/
lemma positiveRational_cpow_I_ne_one
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    (((a : ℂ) / (b : ℂ)) ^ Complex.I) ≠ 1 := by
  have halg : IsAlgebraic ℚ ((a : ℂ) / (b : ℂ)) :=
    (RHTower.isAlgebraic_natComplex a).mul (RHTower.isAlgebraic_natComplex b).inv
  have hzero : (a : ℂ) / (b : ℂ) ≠ 0 :=
    div_ne_zero (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')
  have hone : (a : ℂ) / (b : ℂ) ≠ 1 := by
    intro h
    have hc : (a : ℂ) = (b : ℂ) :=
      (div_eq_one_iff_eq (by exact_mod_cast hb.ne')).mp h
    exact hab (by exact_mod_cast hc)
  have htrans := algebraicBase_imaginaryNatPower_transcendental
    ((a : ℂ) / (b : ℂ)) halg hzero hone (m := 1) (by norm_num)
  intro hpow
  apply htrans
  rw [show ((1 : ℕ) : ℂ) * I = I by norm_num, hpow]
  simpa using (RHTower.isAlgebraic_natComplex 1)

/-- Distinct squarefree prime supports have distinct unitary time-one modes.  Unique factorization
reduces equality to a nontrivial positive rational `I`-power, excluded by Gelfond--Schneider. -/
lemma finitePrimeSquarefreeLoschmidtMode_injective :
    Function.Injective finitePrimeSquarefreeLoschmidtMode := by
  intro T U hTU
  let a : ℕ := ∏ p ∈ T, (p : ℕ)
  let b : ℕ := ∏ p ∈ U, (p : ℕ)
  have ha : 0 < a := finitePrimeSquarefreeProduct_pos T
  have hb : 0 < b := finitePrimeSquarefreeProduct_pos U
  have hab : a = b := by
    by_contra hab
    have hpow : (((a : ℂ) / (b : ℂ)) ^ Complex.I) = 1 := by
      rw [Complex.cpow_def_of_ne_zero
        (div_ne_zero (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne'))]
      rw [show ((a : ℂ) / (b : ℂ)) =
          (((a : ℝ) / (b : ℝ) : ℝ) : ℂ) by push_cast; ring]
      have hlog : Complex.log ((((a : ℝ) / (b : ℝ) : ℝ) : ℂ)) =
          (Real.log ((a : ℝ) / (b : ℝ)) : ℂ) :=
        (Complex.ofReal_log
          (div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b))).symm
      rw [hlog]
      rw [Real.log_div (by positivity) (by positivity)]
      rw [Complex.ofReal_sub]
      change Complex.exp
        (((Real.log a : ℂ) - (Real.log b : ℂ)) * I) = 1
      rw [show ((Real.log a : ℂ) - (Real.log b : ℂ)) * I =
          (Real.log a : ℂ) * I + (-((Real.log b : ℂ) * I)) by ring,
        Complex.exp_add]
      have hphase :
          Complex.exp (-((Real.log a : ℝ) : ℂ) * I) =
            Complex.exp (-((Real.log b : ℝ) : ℂ) * I) := by
        simpa [finitePrimeSquarefreeLoschmidtMode, a, b] using hTU
      calc
        Complex.exp ((Real.log a : ℂ) * I) *
            Complex.exp (-((Real.log b : ℂ) * I)) =
            Complex.exp ((Real.log a : ℂ) * I) *
              Complex.exp (-((Real.log a : ℂ) * I)) := by
                have haNeg : -((Real.log a : ℂ) * I) =
                    -((Real.log a : ℂ)) * I := by ring
                have hbNeg : -((Real.log b : ℂ) * I) =
                    -((Real.log b : ℂ)) * I := by ring
                rw [haNeg, hbNeg, hphase]
        _ = 1 := by rw [← Complex.exp_add]; simp
    exact (positiveRational_cpow_I_ne_one ha hb hab) hpow
  exact GaloisForLFunctions.RHTower.primeSupportProduct_injective hab

/-- The signed diagonal weight of one squarefree Loschmidt energy level. -/
def finitePrimeSquarefreeLoschmidtCoefficient
    (S : Finset Nat.Primes) (sigma : ℝ) (T : Finset Nat.Primes) : ℂ :=
  ((-1 : ℂ) ^ T.card) * (finitePrimeSquarefreeProbability S sigma T : ℂ)

/-- At imaginary integer time, one signed squarefree term is its diagonal weight times its
unitary mode to that integer time. -/
lemma finitePrimeSignedSquarefreeTerm_imaginaryNat
    (sigma : ℝ) (T : Finset Nat.Primes) (n : ℕ) :
    finitePrimeSignedSquarefreeTerm sigma (((n : ℕ) : ℂ) * Complex.I) T =
      ((-1 : ℂ) ^ T.card *
          ((∏ p ∈ T, primeSchurWeight sigma p : ℝ) : ℂ)) *
        finitePrimeSquarefreeLoschmidtMode T ^ n := by
  classical
  have hlocal (p : Nat.Primes) :
      Complex.exp (-(Real.log (p : ℝ) : ℂ) * (((n : ℕ) : ℂ) * I)) =
        Complex.exp (-((Real.log (p : ℝ) : ℂ)) * I) ^ n := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [finitePrimeSignedSquarefreeTerm,
    finitePrimeSquarefreeLoschmidtMode_eq_prod]
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_neg]
  rw [Finset.prod_pow]
  push_cast
  ring

/-- Squared magnitude of a Loschmidt coefficient is the square of its Bernoulli probability. -/
lemma norm_finitePrimeSquarefreeLoschmidtCoefficient_sq
    (S : Finset Nat.Primes) (sigma : ℝ) (T : Finset Nat.Primes) :
    ‖finitePrimeSquarefreeLoschmidtCoefficient S sigma T‖ ^ (2 : ℕ) =
      finitePrimeSquarefreeProbability S sigma T ^ (2 : ℕ) := by
  have hP := finitePrimeSquarefreeProbability_nonneg S sigma T
  rw [finitePrimeSquarefreeLoschmidtCoefficient, norm_mul, norm_pow,
    norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hP]

/-- Exact value relation: the finite signed prime transfer on imaginary integer time is the finite
exponential pencil of its squarefree Loschmidt spectrum. -/
theorem finitePrimeSignedSchurTransfer_imaginaryNat_eq_exponentialPencil
    (S : Finset Nat.Primes) (sigma : ℝ) (n : ℕ) :
    finitePrimeSignedSchurTransfer S sigma (((n : ℕ) : ℂ) * Complex.I) =
      finiteExponentialPencil S.powerset
        (finitePrimeSquarefreeLoschmidtCoefficient S sigma)
        finitePrimeSquarefreeLoschmidtMode n := by
  classical
  rw [finitePrimeSignedSchurTransfer_squarefreeExpansion,
    finiteExponentialPencil, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro T hT
  rw [finitePrimeSignedSquarefreeTerm_imaginaryNat]
  rw [finitePrimeSquarefreeLoschmidtCoefficient,
    finitePrimeSquarefreeProbability, finitePrimeSignedSchurDenominator]
  push_cast
  ring

/-- Purity of the dephased squarefree Bernoulli state underlying the signed prime transfer. -/
def finitePrimeSquarefreeLoschmidtPurity
    (S : Finset Nat.Primes) (sigma : ℝ) : ℝ :=
  ∑ T : ↥S.powerset, ‖finitePrimeSquarefreeAmplitude S sigma T‖ ^ (4 : ℕ)

/-- The dephased-state purity is the squarefree Bernoulli collision probability. -/
theorem finitePrimeSquarefreeLoschmidtPurity_eq_probability_sq
    (S : Finset Nat.Primes) (sigma : ℝ) :
    finitePrimeSquarefreeLoschmidtPurity S sigma =
      ∑ T ∈ S.powerset, finitePrimeSquarefreeProbability S sigma T ^ (2 : ℕ) := by
  classical
  rw [finitePrimeSquarefreeLoschmidtPurity, Finset.univ_eq_attach]
  calc
    (∑ T ∈ S.powerset.attach,
        ‖finitePrimeSquarefreeAmplitude S sigma T‖ ^ (4 : ℕ)) =
        ∑ T ∈ S.powerset.attach,
          finitePrimeSquarefreeProbability S sigma T.1 ^ (2 : ℕ) := by
            apply Finset.sum_congr rfl
            intro T hT
            have h := norm_finitePrimeSquarefreeAmplitude_sq S sigma T
            calc
              ‖finitePrimeSquarefreeAmplitude S sigma T‖ ^ (4 : ℕ) =
                  (‖finitePrimeSquarefreeAmplitude S sigma T‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
              _ = finitePrimeSquarefreeProbability S sigma T.1 ^ (2 : ℕ) := by rw [h]
    _ = ∑ T ∈ S.powerset,
        finitePrimeSquarefreeProbability S sigma T ^ (2 : ℕ) := by
          exact Finset.sum_attach S.powerset
            (fun T => finitePrimeSquarefreeProbability S sigma T ^ (2 : ℕ))

/-- Every finite squarefree Loschmidt state has strictly positive purity. -/
theorem finitePrimeSquarefreeLoschmidtPurity_pos
    (S : Finset Nat.Primes) (sigma : ℝ) :
    0 < finitePrimeSquarefreeLoschmidtPurity S sigma := by
  rw [finitePrimeSquarefreeLoschmidtPurity_eq_probability_sq]
  apply Finset.sum_pos'
  · intro T hT
    exact sq_nonneg _
  · refine ⟨∅, by simp, sq_pos_of_pos ?_⟩
    rw [finitePrimeSquarefreeProbability]
    simp only [Finset.prod_empty, one_div]
    exact inv_pos.mpr (Finset.prod_pos fun p _ => by
      linarith [primeSchurWeight_pos sigma p])

/-- Independent-prime factorization of the Loschmidt purity into one-prime collision factors. -/
theorem finitePrimeSquarefreeLoschmidtPurity_eq_prod
    (S : Finset Nat.Primes) (sigma : ℝ) :
    finitePrimeSquarefreeLoschmidtPurity S sigma =
      ∏ p ∈ S,
        (1 + primeSchurWeight sigma p ^ (2 : ℕ)) /
          (1 + primeSchurWeight sigma p) ^ (2 : ℕ) := by
  classical
  rw [finitePrimeSquarefreeLoschmidtPurity_eq_probability_sq]
  let D : ℝ := ∏ p ∈ S, (1 + primeSchurWeight sigma p)
  calc
    (∑ T ∈ S.powerset, finitePrimeSquarefreeProbability S sigma T ^ (2 : ℕ)) =
        (∑ T ∈ S.powerset,
          ∏ p ∈ T, primeSchurWeight sigma p ^ (2 : ℕ)) / D ^ (2 : ℕ) := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro T hT
            rw [finitePrimeSquarefreeProbability, div_pow, Finset.prod_pow]
    _ = (∏ p ∈ S, (1 + primeSchurWeight sigma p ^ (2 : ℕ))) / D ^ (2 : ℕ) := by
          congr 1
          simpa [GaloisForLFunctions.RHProofLab.finiteLocalEulerProduct,
            GaloisForLFunctions.RHProofLab.squarefreeMonomial] using
              (GaloisForLFunctions.RHProofLab.finiteLocalEulerProduct_subsetExpansion
                S (fun p : Nat.Primes => primeSchurWeight sigma p ^ (2 : ℕ))).symm
    _ = ∏ p ∈ S,
        (1 + primeSchurWeight sigma p ^ (2 : ℕ)) /
          (1 + primeSchurWeight sigma p) ^ (2 : ℕ) := by
          rw [Finset.prod_div_distrib, Finset.prod_pow]

/-- The Cesaro mean Loschmidt echo of the finite signed prime transfer converges exactly to the
positive purity of its squarefree Bernoulli state. -/
theorem tendsto_finitePrimeSignedSchurTransfer_imaginaryNat_cesaro_norm_sq
    (S : Finset Nat.Primes) (sigma : ℝ) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ‖finitePrimeSignedSchurTransfer S sigma
          (((n : ℕ) : ℂ) * Complex.I)‖ ^ (2 : ℕ))
      atTop (nhds (finitePrimeSquarefreeLoschmidtPurity S sigma)) := by
  classical
  have h := tendsto_finiteExponentialPencil_cesaro_norm_sq S.powerset
    (finitePrimeSquarefreeLoschmidtCoefficient S sigma)
    finitePrimeSquarefreeLoschmidtMode
    (fun T _ => finitePrimeSquarefreeLoschmidtMode_norm T)
    finitePrimeSquarefreeLoschmidtMode_injective.injOn
  rw [finitePrimeSquarefreeLoschmidtPurity_eq_probability_sq]
  convert h using 1
  · funext N
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [finitePrimeSignedSchurTransfer_imaginaryNat_eq_exponentialPencil]
  · apply congrArg nhds
    apply Finset.sum_congr rfl
    intro T hT
    rw [norm_finitePrimeSquarefreeLoschmidtCoefficient_sq]

/-- The vacuum squarefree level has nonzero Loschmidt coefficient. -/
theorem finitePrimeSquarefreeLoschmidtCoefficient_empty_ne_zero
    (S : Finset Nat.Primes) (sigma : ℝ) :
    finitePrimeSquarefreeLoschmidtCoefficient S sigma ∅ ≠ 0 := by
  rw [finitePrimeSquarefreeLoschmidtCoefficient]
  norm_num [finitePrimeSquarefreeProbability]
  exact Finset.prod_ne_zero_iff.mpr fun p _ => by
    have hp := primeSchurWeight_pos sigma p
    exact_mod_cast (by linarith : (1 + primeSchurWeight sigma p) ≠ 0)

/-- A finite signed prime transfer cannot disappear along imaginary integer time by destructive
phase cancellation. -/
theorem not_tendsto_finitePrimeSignedSchurTransfer_imaginaryNat_zero
    (S : Finset Nat.Primes) (sigma : ℝ) :
    ¬ Tendsto
      (fun n : ℕ => finitePrimeSignedSchurTransfer S sigma
        (((n : ℕ) : ℂ) * Complex.I)) atTop (nhds 0) := by
  intro hzero
  apply not_tendsto_finiteExponentialPencil_zero S.powerset
    (finitePrimeSquarefreeLoschmidtCoefficient S sigma)
    finitePrimeSquarefreeLoschmidtMode
    (fun T _ => finitePrimeSquarefreeLoschmidtMode_norm T)
    finitePrimeSquarefreeLoschmidtMode_injective.injOn
    ⟨∅, by simp, finitePrimeSquarefreeLoschmidtCoefficient_empty_ne_zero S sigma⟩
  convert hzero using 1
  funext n
  exact (finitePrimeSignedSchurTransfer_imaginaryNat_eq_exponentialPencil
    S sigma n).symm

end

end RHTower
