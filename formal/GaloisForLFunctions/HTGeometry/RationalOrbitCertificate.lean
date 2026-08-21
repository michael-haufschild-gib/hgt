/-
# A decidable certificate for endpoint circuit hardness

At rational coefficients and a rational time the Schrödinger generator of the Pauli ensemble is one
rational scalar times a Gaussian-integer matrix, so every truncation of its exponential series acts
on the all-zero product state by exact rational arithmetic.  Truncation error is controlled by the
factorial remainder and the dictionary is presented by rational approximants, so "the endpoint
misses every target by more than `ε`" has a purely rational sufficient condition.  That condition is
decidable, it is sound, and -- because a strict miss leaves a margin -- every genuine witness
satisfies it at some finite truncation order and approximation level.

Main results:
* `certOrbit` — the rational truncated orbit, and `ratVecToC_certOrbit` its correctness.
* `HardCertificate` — **the decidable certificate**.
* `hardCircuitEvent_of_hardCertificate` — **soundness**.
* `exists_hardCertificate_of_hard` — **completeness at finite precision**.
-/
import GaloisForLFunctions.HTGeometry.GaussianIntegerPauliModel
import GaloisForLFunctions.HTGeometry.ExponentialFactorialRemainder
import GaloisForLFunctions.HTGeometry.CommonTimeCircuitHardness
import GaloisForLFunctions.HTGeometry.RationalCommonTimeWitness

open Matrix Finset
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-! ## Rational complex vectors -/

section RatVec

variable {d : Type} [Fintype d] [DecidableEq d]

/-- A complex register vector presented by its rational real and imaginary parts. -/
def ratVecToC (v : (d → ℚ) × (d → ℚ)) : d → ℂ :=
  fun i => ((v.1 i : ℚ) : ℂ) + ((v.2 i : ℚ) : ℂ) * Complex.I

/-- The squared Euclidean distance of two rational register vectors. -/
def ratSqDist (u v : (d → ℚ) × (d → ℚ)) : ℚ :=
  ∑ i, ((u.1 i - v.1 i) ^ 2 + (u.2 i - v.2 i) ^ 2)

theorem ratSqDist_nonneg (u v : (d → ℚ) × (d → ℚ)) : 0 ≤ ratSqDist u v :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem ratSqDist_eq_dist_sq (u v : (d → ℚ) × (d → ℚ)) :
    ((ratSqDist u v : ℚ) : ℝ)
      = dist (eucVec (ratVecToC u)) (eucVec (ratVecToC v)) ^ 2 := by
  rw [dist_eucVec, Real.sq_sqrt (by positivity), ratSqDist]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [ratVecToC, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ratCast_re,
    Complex.ratCast_im]
  ring

end RatVec

/-! ## The rational model of the truncated orbit -/

section Model

variable {n : ℕ}

/-- The common denominator of the coefficient products. -/
def coeffDen (wq Jq : (Fin n → Option (Fin 3)) → ℚ) : ℕ := ∏ P, (wq P * Jq P).den

theorem coeffDen_pos (wq Jq : (Fin n → Option (Fin 3)) → ℚ) : 0 < coeffDen wq Jq :=
  Finset.prod_pos fun P _ => (wq P * Jq P).pos

/-- The integer numerators of the coefficient products over their common denominator. -/
def coeffNum (wq Jq : (Fin n → Option (Fin 3)) → ℚ) : (Fin n → Option (Fin 3)) → ℤ :=
  fun P => (((coeffDen wq Jq : ℚ)) * (wq P * Jq P)).num

theorem coeffNum_spec (wq Jq : (Fin n → Option (Fin 3)) → ℚ) (P : Fin n → Option (Fin 3)) :
    ((coeffNum wq Jq P : ℤ) : ℚ) = ((coeffDen wq Jq : ℚ)) * (wq P * Jq P) := by
  classical
  obtain ⟨m, hm⟩ : (wq P * Jq P).den ∣ coeffDen wq Jq :=
    Finset.dvd_prod_of_mem (fun Q => (wq Q * Jq Q).den) (Finset.mem_univ P)
  have hz : ((coeffDen wq Jq : ℚ)) * (wq P * Jq P)
      = (((wq P * Jq P).num * m : ℤ) : ℚ) := by
    rw [coeffDen] at hm ⊢
    rw [hm]
    push_cast
    linear_combination (m : ℚ) * Rat.mul_den_eq_num (wq P * Jq P)
  rw [coeffNum, hz, Rat.num_intCast]

/-- The Gaussian-integer generator of the Schrödinger flow: `-i` times the cleared Hamiltonian. -/
def certGen (wq Jq : (Fin n → Option (Fin 3)) → ℚ) :
    Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) GaussianInt :=
  (⟨0, -1⟩ : GaussianInt) • gaussPauliEnsemble (coeffNum wq Jq)

/-- The rational scale that restores the generator. -/
def certScale (wq Jq : (Fin n → Option (Fin 3)) → ℚ) (τ : ℚ) : ℚ := τ / (coeffDen wq Jq : ℚ)

/-- The Schrödinger generator at rational data. -/
theorem smul_map_certGen (wq Jq : (Fin n → Option (Fin 3)) → ℚ) (τ : ℚ) :
    ((certScale wq Jq τ : ℚ) : ℂ) • ((certGen wq Jq).map GaussianInt.toComplex)
      = (τ : ℝ) • ((-Complex.I) •
          pauliEnsemble (fun P => (wq P : ℝ)) (fun P => (Jq P : ℝ))) := by
  classical
  have hDpos : (0 : ℝ) < (coeffDen wq Jq : ℝ) := by
    exact_mod_cast coeffDen_pos wq Jq
  have hDne : ((coeffDen wq Jq : ℝ)) ≠ 0 := ne_of_gt hDpos
  have hham := pauliEnsemble_eq_smul_map_gaussPauliEnsemble
    (fun P => (wq P : ℝ)) (fun P => (Jq P : ℝ)) (coeffNum wq Jq) hDne
    (fun P => by exact_mod_cast (coeffNum_spec wq Jq P).symm)
  have hgen : (certGen wq Jq).map GaussianInt.toComplex
      = (-Complex.I) • ((gaussPauliEnsemble (coeffNum wq Jq)).map GaussianInt.toComplex) := by
    ext x y
    simp only [certGen, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    rw [map_mul]
    congr 1
    rw [GaussianInt.toComplex_def']
    push_cast
    ring
  have hreal : ∀ (r : ℝ) (M : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ), r • M = ((r : ℂ)) • M := by
    intro r M
    ext x y
    simp [Matrix.smul_apply, Complex.real_smul]
  rw [hgen, hham]
  simp only [hreal]
  rw [smul_smul, smul_smul, smul_smul]
  congr 1
  rw [certScale]
  push_cast
  field_simp

end Model


/-! ## The truncated orbit in exact rational arithmetic -/

section Orbit

variable {n : ℕ}

/-- The image of a matrix action under a ring homomorphism. -/
theorem map_mulVec_map {d : Type} [Fintype d] {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix d d R) (v : d → R) (i : d) :
    ((A.map f) *ᵥ (fun j => f (v j))) i = f ((A *ᵥ v) i) := by
  show (∑ j, f (A i j) * f (v j)) = f (∑ j, A i j * v j)
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => (map_mul f _ _).symm

/-- The Gaussian-integer iterates of the seed under the cleared generator. -/
def certIter (wq Jq : (Fin n → Option (Fin 3)) → ℚ) (k : ℕ) :
    FiniteQubitConfiguration (Fin n) → GaussianInt :=
  (certGen wq Jq) ^ k *ᵥ gaussZeroProductState

/-- The rational coefficient of the `k`-th term of the truncated series. -/
def certTerm (wq Jq : (Fin n → Option (Fin 3)) → ℚ) (τ : ℚ) (k : ℕ) : ℚ :=
  (certScale wq Jq τ) ^ k / (Nat.factorial k)

/-- The truncated orbit of the seed, in exact rational arithmetic. -/
def certOrbit (wq Jq : (Fin n → Option (Fin 3)) → ℚ) (τ : ℚ) (N : ℕ) :
    (FiniteQubitConfiguration (Fin n) → ℚ) × (FiniteQubitConfiguration (Fin n) → ℚ) :=
  (fun i => ∑ k ∈ Finset.range N, certTerm wq Jq τ k * ((certIter wq Jq k) i).re,
   fun i => ∑ k ∈ Finset.range N, certTerm wq Jq τ k * ((certIter wq Jq k) i).im)

/-- **The rational truncated orbit is the truncated series applied to the seed.** -/
theorem ratVecToC_certOrbit (wq Jq : (Fin n → Option (Fin 3)) → ℚ) (τ : ℚ) (N : ℕ) :
    ratVecToC (certOrbit wq Jq τ N)
      = (∑ k ∈ Finset.range N, ((Nat.factorial k : ℂ))⁻¹ •
          (((certScale wq Jq τ : ℚ) : ℂ) •
            ((certGen wq Jq).map GaussianInt.toComplex)) ^ k) *ᵥ zeroProductState (Fin n) := by
  classical
  funext i
  have hOmega : (zeroProductState (Fin n))
      = fun x => GaussianInt.toComplex (gaussZeroProductState x) := by
    funext x
    exact (map_gaussZeroProductState x).symm
  have hpow : ∀ k : ℕ,
      (((certScale wq Jq τ : ℚ) : ℂ) • ((certGen wq Jq).map GaussianInt.toComplex)) ^ k
        = ((certScale wq Jq τ : ℚ) : ℂ) ^ k •
            (((certGen wq Jq) ^ k).map GaussianInt.toComplex) := by
    intro k
    rw [smul_pow]
    congr 1
    exact (map_pow (GaussianInt.toComplex.mapMatrix) (certGen wq Jq) k).symm
  rw [sum_mulVec]
  have hterm : ∀ k ∈ Finset.range N,
      ((((Nat.factorial k : ℂ))⁻¹ •
          (((certScale wq Jq τ : ℚ) : ℂ) •
            ((certGen wq Jq).map GaussianInt.toComplex)) ^ k) *ᵥ zeroProductState (Fin n)) i
        = ((certTerm wq Jq τ k : ℚ) : ℂ) *
            GaussianInt.toComplex (certIter wq Jq k i) := by
    intro k _
    rw [hpow k, smul_smul, smul_mulVec]
    have hact : ((((certGen wq Jq) ^ k).map GaussianInt.toComplex) *ᵥ
        zeroProductState (Fin n)) i = GaussianInt.toComplex (certIter wq Jq k i) := by
      rw [hOmega, certIter]
      exact map_mulVec_map GaussianInt.toComplex ((certGen wq Jq) ^ k) gaussZeroProductState i
    rw [Pi.smul_apply, hact, smul_eq_mul]
    congr 1
    rw [certTerm]
    push_cast
    ring
  rw [Finset.sum_apply, Finset.sum_congr rfl hterm]
  simp only [ratVecToC, certOrbit]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show GaussianInt.toComplex (certIter wq Jq k i)
      = ((certIter wq Jq k i).re : ℂ) + ((certIter wq Jq k i).im : ℂ) * Complex.I from
    GaussianInt.toComplex_def _]
  ring

end Orbit


/-! ## The certificate -/

section Certificate

variable {n : ℕ} {C : Type} [Fintype C]

/-- A rational bound on the size of the Schrödinger generator. -/
def certBound (wq Jq : (Fin n → Option (Fin 3)) → ℚ) (τ : ℚ) : ℚ :=
  |τ| * ∑ P, |wq P * Jq P|

theorem certBound_nonneg (wq Jq : (Fin n → Option (Fin 3)) → ℚ) (τ : ℚ) :
    0 ≤ certBound wq Jq τ :=
  mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- The rational truncation remainder at order `N`. -/
def certRemainder (wq Jq : (Fin n → Option (Fin 3)) → ℚ) (τ : ℚ) (N : ℕ) : ℚ :=
  2 * (certBound wq Jq τ) ^ N / (Nat.factorial N)

theorem certRemainder_nonneg (wq Jq : (Fin n → Option (Fin 3)) → ℚ) (τ : ℚ) (N : ℕ) :
    0 ≤ certRemainder wq Jq τ N := by
  rw [certRemainder]
  have := certBound_nonneg wq Jq τ
  positivity

/-- **The certificate.**  A purely rational sufficient condition for the endpoint of the rational
autonomous evolution to miss every dictionary target by more than `eps`. -/
def HardCertificate (wq Jq : (Fin n → Option (Fin 3)) → ℚ) (τ : ℚ) (eps : ℚ)
    (Zapp : C → ℕ → (FiniteQubitConfiguration (Fin n) → ℚ) ×
      (FiniteQubitConfiguration (Fin n) → ℚ)) (N mm : ℕ) : Prop :=
  0 < τ ∧ 2 * certBound wq Jq τ ≤ (N : ℚ) + 1 ∧
    ∀ κ, (eps + certRemainder wq Jq τ N + 1 / ((mm : ℚ) + 1)) ^ 2
      < ratSqDist (certOrbit wq Jq τ N) (Zapp κ mm)

instance decidableHardCertificate (wq Jq : (Fin n → Option (Fin 3)) → ℚ) (τ eps : ℚ)
    (Zapp : C → ℕ → (FiniteQubitConfiguration (Fin n) → ℚ) ×
      (FiniteQubitConfiguration (Fin n) → ℚ)) (N mm : ℕ) :
    Decidable (HardCertificate wq Jq τ eps Zapp N mm) := by
  unfold HardCertificate
  infer_instance

/-- The Schrödinger generator of the rational data. -/
def certFlow (wq Jq : (Fin n → Option (Fin 3)) → ℚ) (τ : ℚ) :
    Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ :=
  (τ : ℝ) • ((-Complex.I) • pauliEnsemble (fun P => (wq P : ℝ)) (fun P => (Jq P : ℝ)))

theorem norm_certFlow_le (wq Jq : (Fin n → Option (Fin 3)) → ℚ) (τ : ℚ) :
    ‖certFlow wq Jq τ‖ ≤ ((certBound wq Jq τ : ℚ) : ℝ) := by
  have hI : ‖(-Complex.I) • pauliEnsemble (fun P => (wq P : ℝ)) (fun P => (Jq P : ℝ))‖
      = ‖pauliEnsemble (fun P => (wq P : ℝ)) (fun P => (Jq P : ℝ))‖ := by
    rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
  have hH : ‖pauliEnsemble (fun P => (wq P : ℝ)) (fun P => (Jq P : ℝ))‖
      ≤ ∑ P, |(wq P : ℝ) * (Jq P : ℝ)| := by
    refine le_trans (opNorm_pauliCombination_le (σ := Fin n) _) (le_of_eq ?_)
    exact Finset.sum_congr rfl fun P _ => by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [certFlow, norm_smul, Real.norm_eq_abs, hI, certBound]
  push_cast
  exact mul_le_mul_of_nonneg_left hH (abs_nonneg _)

/-- The truncated series of the generator. -/
def certPartial (wq Jq : (Fin n → Option (Fin 3)) → ℚ) (τ : ℚ) (N : ℕ) :
    Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ :=
  ∑ k ∈ Finset.range N, ((Nat.factorial k : ℂ))⁻¹ • (certFlow wq Jq τ) ^ k

theorem ratVecToC_certOrbit_eq (wq Jq : (Fin n → Option (Fin 3)) → ℚ) (τ : ℚ) (N : ℕ) :
    ratVecToC (certOrbit wq Jq τ N)
      = (certPartial wq Jq τ N) *ᵥ zeroProductState (Fin n) := by
  rw [ratVecToC_certOrbit, certPartial, certFlow, ← smul_map_certGen]

theorem dist_orbit_certOrbit_le (wq Jq : (Fin n → Option (Fin 3)) → ℚ) (τ : ℚ) (N : ℕ)
    (hN : 2 * ((certBound wq Jq τ : ℚ) : ℝ) ≤ (N : ℝ) + 1) :
    dist (orbitVec (pauliEnsemble (fun P => (wq P : ℝ)) (fun P => (Jq P : ℝ)))
        (zeroProductState (Fin n)) (τ : ℝ))
      (eucVec (ratVecToC (certOrbit wq Jq τ N)))
      ≤ ((certRemainder wq Jq τ N : ℚ) : ℝ) := by
  have hOmega : finiteComplexInner (zeroProductState (Fin n)) (zeroProductState (Fin n)) = 1 := by
    rw [finiteComplexInner_self_eq_sum_normSq, sum_normSq_zeroProductState]
    norm_num
  have hnorm1 : ‖eucVec (zeroProductState (Fin n))‖ = 1 := norm_eucVec_eq_one hOmega
  have hexp : orbitVec (pauliEnsemble (fun P => (wq P : ℝ)) (fun P => (Jq P : ℝ)))
      (zeroProductState (Fin n)) (τ : ℝ)
      = eucVec (NormedSpace.exp (certFlow wq Jq τ) *ᵥ zeroProductState (Fin n)) := rfl
  rw [hexp, ratVecToC_certOrbit_eq, dist_eq_norm]
  have hsub : eucVec (NormedSpace.exp (certFlow wq Jq τ) *ᵥ zeroProductState (Fin n))
      - eucVec ((certPartial wq Jq τ N) *ᵥ zeroProductState (Fin n))
      = eucVec ((NormedSpace.exp (certFlow wq Jq τ) - certPartial wq Jq τ N) *ᵥ
          zeroProductState (Fin n)) := by
    rw [Matrix.sub_mulVec, eucVec, eucVec, eucVec, map_sub]
  rw [hsub]
  refine le_trans (Matrix.l2_opNorm_mulVec _ (eucVec (zeroProductState (Fin n)))) ?_
  rw [hnorm1, mul_one]
  have hrem := norm_exp_sub_partialSum_le (certFlow wq Jq τ) N
    (norm_certFlow_le wq Jq τ) hN
  refine le_trans hrem (le_of_eq ?_)
  rw [certRemainder]
  push_cast
  ring

end Certificate


/-! ## Soundness and completeness -/

section SoundComplete

variable {n : ℕ} {C : Type} [Fintype C]

/-- **Soundness.**  A certificate exhibits a genuine hard witness. -/
theorem hardCircuitEvent_of_hardCertificate
    {wq Jq : (Fin n → Option (Fin 3)) → ℚ} {τ eps : ℚ}
    {Z : C → (FiniteQubitConfiguration (Fin n) → ℂ)}
    {Zapp : C → ℕ → (FiniteQubitConfiguration (Fin n) → ℚ) ×
      (FiniteQubitConfiguration (Fin n) → ℚ)}
    (hZapp : ∀ κ mm, dist (eucVec (Z κ)) (eucVec (ratVecToC (Zapp κ mm)))
      ≤ 1 / ((mm : ℝ) + 1))
    {N mm : ℕ} (heps : 0 ≤ eps) (h : HardCertificate wq Jq τ eps Zapp N mm) :
    ((fun P => (Jq P : ℝ)), (τ : ℝ))
      ∈ hardCircuitEvent (fun P => (wq P : ℝ)) (zeroProductState (Fin n)) (eps : ℝ) Z := by
  obtain ⟨-, hN, hcert⟩ := h
  have hNr : 2 * ((certBound wq Jq τ : ℚ) : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hN
  have hrem := dist_orbit_certOrbit_le wq Jq τ N hNr
  rintro ⟨κ, hκ⟩
  have hc := hcert κ
  have hA0 : (0 : ℝ) ≤ ((eps + certRemainder wq Jq τ N + 1 / ((mm : ℚ) + 1) : ℚ) : ℝ) := by
    have h1 : (0 : ℚ) ≤ certRemainder wq Jq τ N := certRemainder_nonneg wq Jq τ N
    have h2 : (0 : ℚ) ≤ 1 / ((mm : ℚ) + 1) := by positivity
    have : (0 : ℚ) ≤ eps + certRemainder wq Jq τ N + 1 / ((mm : ℚ) + 1) := by linarith
    exact_mod_cast this
  have hsqr : ((eps + certRemainder wq Jq τ N + 1 / ((mm : ℚ) + 1) : ℚ) : ℝ) ^ 2
      < dist (eucVec (ratVecToC (certOrbit wq Jq τ N)))
          (eucVec (ratVecToC (Zapp κ mm))) ^ 2 := by
    rw [← ratSqDist_eq_dist_sq]
    exact_mod_cast hc
  have hlt : ((eps + certRemainder wq Jq τ N + 1 / ((mm : ℚ) + 1) : ℚ) : ℝ)
      < dist (eucVec (ratVecToC (certOrbit wq Jq τ N))) (eucVec (ratVecToC (Zapp κ mm))) :=
    lt_of_pow_lt_pow_left₀ 2 dist_nonneg hsqr
  have htri := dist_triangle4 (eucVec (ratVecToC (certOrbit wq Jq τ N)))
    (orbitVec (pauliEnsemble (fun P => (wq P : ℝ)) (fun P => (Jq P : ℝ)))
      (zeroProductState (Fin n)) (τ : ℝ))
    (eucVec (Z κ)) (eucVec (ratVecToC (Zapp κ mm)))
  have hcomm : dist (eucVec (ratVecToC (certOrbit wq Jq τ N)))
      (orbitVec (pauliEnsemble (fun P => (wq P : ℝ)) (fun P => (Jq P : ℝ)))
        (zeroProductState (Fin n)) (τ : ℝ))
      = dist (orbitVec (pauliEnsemble (fun P => (wq P : ℝ)) (fun P => (Jq P : ℝ)))
          (zeroProductState (Fin n)) (τ : ℝ)) (eucVec (ratVecToC (certOrbit wq Jq τ N))) :=
    dist_comm _ _
  have happ := hZapp κ mm
  have hcast : ((eps + certRemainder wq Jq τ N + 1 / ((mm : ℚ) + 1) : ℚ) : ℝ)
      = (eps : ℝ) + ((certRemainder wq Jq τ N : ℚ) : ℝ) + 1 / ((mm : ℝ) + 1) := by
    push_cast
    ring
  rw [hcast] at hlt
  rw [hcomm] at htri
  linarith [hlt, htri, hrem, happ, hκ]

/-- **Completeness at finite precision.**  Every genuine hard witness is certified once the
truncation order and the approximation level are large enough. -/
theorem exists_hardCertificate_of_hard [Nonempty C]
    {wq Jq : (Fin n → Option (Fin 3)) → ℚ} {τ eps : ℚ} (hτ : 0 < τ)
    {Z : C → (FiniteQubitConfiguration (Fin n) → ℂ)}
    {Zapp : C → ℕ → (FiniteQubitConfiguration (Fin n) → ℚ) ×
      (FiniteQubitConfiguration (Fin n) → ℚ)}
    (hZapp : ∀ κ mm, dist (eucVec (Z κ)) (eucVec (ratVecToC (Zapp κ mm)))
      ≤ 1 / ((mm : ℝ) + 1))
    (heps : 0 ≤ eps)
    (hhard : ((fun P => (Jq P : ℝ)), (τ : ℝ))
      ∈ hardCircuitEvent (fun P => (wq P : ℝ)) (zeroProductState (Fin n)) (eps : ℝ) Z) :
    ∃ N mm : ℕ, HardCertificate wq Jq τ eps Zapp N mm := by
  classical
  obtain ⟨θ, hθ0, hθ⟩ := exists_uniform_margin (H := pauliEnsemble
    (fun P => (wq P : ℝ)) (fun P => (Jq P : ℝ)))
    (psi := zeroProductState (Fin n)) (eps := (eps : ℝ)) (Z := Z) (t := (τ : ℝ)) hhard
  obtain ⟨mm, hmm⟩ := exists_nat_one_div_lt (show (0 : ℝ) < θ / 6 by linarith)
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = ((certBound wq Jq τ : ℚ) : ℝ) := ⟨_, rfl⟩
  have hb0 : 0 ≤ b := by
    rw [hbdef]
    exact_mod_cast certBound_nonneg wq Jq τ
  have hlim : Filter.Tendsto (fun N : ℕ => 2 * b ^ N / (Nat.factorial N : ℝ))
      Filter.atTop (nhds 0) := by
    have h0 := FloorSemiring.tendsto_pow_div_factorial_atTop b
    have := h0.const_mul (2 : ℝ)
    simpa [mul_div_assoc] using this
  have hev1 : ∀ᶠ N : ℕ in Filter.atTop, 2 * b ^ N / (Nat.factorial N : ℝ) < θ / 6 :=
    hlim.eventually_lt_const (by linarith)
  have hev2 : ∀ᶠ N : ℕ in Filter.atTop, 2 * b ≤ (N : ℝ) + 1 := by
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge (2 * b)
    refine Filter.eventually_atTop.mpr ⟨N₀, fun N hN => ?_⟩
    have : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  obtain ⟨N, hN1, hN2⟩ := (hev1.and hev2).exists
  rw [hbdef] at hN2
  have hNq : 2 * certBound wq Jq τ ≤ (N : ℚ) + 1 := by exact_mod_cast hN2
  have hrem := dist_orbit_certOrbit_le wq Jq τ N hN2
  have hremr : ((certRemainder wq Jq τ N : ℚ) : ℝ) = 2 * b ^ N / (Nat.factorial N : ℝ) := by
    rw [certRemainder, hbdef]
    push_cast
    ring
  refine ⟨N, mm, hτ, hNq, fun κ => ?_⟩
  have happ := hZapp κ mm
  have hbase := hθ κ
  have htri := dist_triangle4
    (orbitVec (pauliEnsemble (fun P => (wq P : ℝ)) (fun P => (Jq P : ℝ)))
      (zeroProductState (Fin n)) (τ : ℝ))
    (eucVec (ratVecToC (certOrbit wq Jq τ N)))
    (eucVec (ratVecToC (Zapp κ mm))) (eucVec (Z κ))
  have hcomm : dist (eucVec (ratVecToC (Zapp κ mm))) (eucVec (Z κ))
      = dist (eucVec (Z κ)) (eucVec (ratVecToC (Zapp κ mm))) := dist_comm _ _
  rw [hcomm] at htri
  have hA0 : (0 : ℝ) ≤ (eps : ℝ) + ((certRemainder wq Jq τ N : ℚ) : ℝ) + 1 / ((mm : ℝ) + 1) := by
    have h1 : (0 : ℝ) ≤ ((certRemainder wq Jq τ N : ℚ) : ℝ) := by
      exact_mod_cast certRemainder_nonneg wq Jq τ N
    have h2 : (0 : ℝ) ≤ 1 / ((mm : ℝ) + 1) := by positivity
    have h3 : (0 : ℝ) ≤ (eps : ℝ) := by exact_mod_cast heps
    linarith
  have hgap : (eps : ℝ) + ((certRemainder wq Jq τ N : ℚ) : ℝ) + 1 / ((mm : ℝ) + 1)
      < dist (eucVec (ratVecToC (certOrbit wq Jq τ N))) (eucVec (ratVecToC (Zapp κ mm))) := by
    rw [hremr]
    linarith [htri, hrem, happ, hbase, hmm, hN1]
  have hsq : ((eps + certRemainder wq Jq τ N + 1 / ((mm : ℚ) + 1) : ℚ) : ℝ) ^ 2
      < ((ratSqDist (certOrbit wq Jq τ N) (Zapp κ mm) : ℚ) : ℝ) := by
    rw [ratSqDist_eq_dist_sq]
    have hcast : ((eps + certRemainder wq Jq τ N + 1 / ((mm : ℚ) + 1) : ℚ) : ℝ)
        = (eps : ℝ) + ((certRemainder wq Jq τ N : ℚ) : ℝ) + 1 / ((mm : ℝ) + 1) := by
      push_cast
      ring
    rw [hcast]
    exact pow_lt_pow_left₀ hgap hA0 (by norm_num)
  exact_mod_cast hsq

end SoundComplete


/-! ## The terminating search -/

section Search

variable {n q : ℕ} {C : Type} [Fintype C] [Nonempty C]

/-- The search space of the witness-selection algorithm: a truncation order, an approximation
level, a rational coefficient vector and a rational time. -/
abbrev CertIndex (n : ℕ) : Type := ℕ × ℕ × ((Fin n → Option (Fin 3)) → ℚ) × ℚ

instance instInhabitedCertIndex : Inhabited (CertIndex n) := ⟨(0, 0, fun _ => 0, 0)⟩

/-- The enumeration the search runs over. -/
def certEnum (n : ℕ) (k : ℕ) : CertIndex n :=
  (Encodable.decode (α := CertIndex n) k).getD default

theorem certEnum_surjective (n : ℕ) : Function.Surjective (certEnum n) := by
  intro x
  refine ⟨Encodable.encode x, ?_⟩
  rw [certEnum, Encodable.encodek]
  rfl

/-- The predicate the search tests: a decidable rational condition. -/
def CertifiedIndex (wq : (Fin n → Option (Fin 3)) → ℚ) (eps : ℚ)
    (Zapp : C → ℕ → (FiniteQubitConfiguration (Fin n) → ℚ) ×
      (FiniteQubitConfiguration (Fin n) → ℚ)) (x : CertIndex n) : Prop :=
  HardCertificate wq x.2.2.1 x.2.2.2 eps Zapp x.1 x.2.1

instance decidableCertifiedIndex (wq : (Fin n → Option (Fin 3)) → ℚ) (eps : ℚ)
    (Zapp : C → ℕ → (FiniteQubitConfiguration (Fin n) → ℚ) ×
      (FiniteQubitConfiguration (Fin n) → ℚ)) :
    DecidablePred (CertifiedIndex wq eps Zapp) := fun x => by
  unfold CertifiedIndex
  infer_instance

/-- **A certified index is a rational autonomous witness.** -/
theorem hard_of_certifiedIndex
    {wq : (Fin n → Option (Fin 3)) → ℚ} {eps : ℚ} (heps : 0 ≤ eps)
    {Z : C → (FiniteQubitConfiguration (Fin n) → ℂ)}
    {Zapp : C → ℕ → (FiniteQubitConfiguration (Fin n) → ℚ) ×
      (FiniteQubitConfiguration (Fin n) → ℚ)}
    (hZapp : ∀ κ mm, dist (eucVec (Z κ)) (eucVec (ratVecToC (Zapp κ mm)))
      ≤ 1 / ((mm : ℝ) + 1))
    {x : CertIndex n} (h : CertifiedIndex wq eps Zapp x) :
    0 < x.2.2.2 ∧
      ((fun P => ((x.2.2.1 P : ℚ) : ℝ)), ((x.2.2.2 : ℚ) : ℝ))
        ∈ hardCircuitEvent (fun P => (wq P : ℝ)) (zeroProductState (Fin n))
          ((eps : ℚ) : ℝ) Z :=
  ⟨h.1, hardCircuitEvent_of_hardCertificate hZapp heps h⟩

/-- **The search terminates.**  Under the hypotheses of the common-time law there is an index of
the enumeration whose rational certificate holds; the first such index is therefore found by an
unbounded search over a decidable predicate. -/
theorem exists_certifiedIndex
    (wq : (Fin n → Option (Fin 3)) → ℚ) (hq : 2 ≤ q)
    (hwsupp : SupportInvariantWeight (fun P => (wq P : ℝ)))
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → (wq P : ℝ) = 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      ((wq (((pauliTracelessLabelEquivFin n q).symm t).1) : ℝ)) ≠ 0)
    (hcard0 : 0 < Fintype.card (Fin n → Option (Fin 3)))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : 2 * Real.log (8 * Fintype.card (Fin n → Option (Fin 3))) ≤ B ^ 2)
    (Z : C → (FiniteQubitConfiguration (Fin n) → ℂ))
    (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    (Zapp : C → ℕ → (FiniteQubitConfiguration (Fin n) → ℚ) ×
      (FiniteQubitConfiguration (Fin n) → ℚ))
    (hZapp : ∀ κ mm, dist (eucVec (Z κ)) (eucVec (ratVecToC (Zapp κ mm)))
      ≤ 1 / ((mm : ℝ) + 1))
    {eps : ℚ} (heps0 : 0 ≤ eps) (heps1 : eps < 1)
    {r : ℕ} (hr : 1 ≤ r)
    (hscale : 16 * (4 * (2 / 3 : ℝ) ^ n) / (1 - ((eps : ℚ) : ℝ) ^ 2) ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2)
    (horizon : ℝ) :
    ∃ k : ℕ, CertifiedIndex wq eps Zapp (certEnum n k) := by
  have hepsR0 : (0 : ℝ) ≤ ((eps : ℚ) : ℝ) := by exact_mod_cast heps0
  have hepsR1 : ((eps : ℚ) : ℝ) < 1 := by exact_mod_cast heps1
  obtain ⟨τ, Jq, -, hτpos, -, -, hhard⟩ := exists_rational_common_time_witness
    (fun P => (wq P : ℝ)) hq hwsupp hw hwne hcard0 hB0 hB Z hZ hepsR0 hepsR1 hr hscale hM hcard
    hs horizon
  obtain ⟨N, mm, hcert⟩ := exists_hardCertificate_of_hard (Zapp := Zapp) hτpos hZapp heps0 hhard
  obtain ⟨k, hk⟩ := certEnum_surjective n (N, mm, Jq, τ)
  exact ⟨k, by rw [CertifiedIndex, hk]; exact hcert⟩

/-- The index the search returns: the least index of the enumeration whose rational certificate
holds. -/
def searchIndex {wq : (Fin n → Option (Fin 3)) → ℚ} {eps : ℚ}
    {Zapp : C → ℕ → (FiniteQubitConfiguration (Fin n) → ℚ) ×
      (FiniteQubitConfiguration (Fin n) → ℚ)}
    (h : ∃ k : ℕ, CertifiedIndex wq eps Zapp (certEnum n k)) : ℕ :=
  Nat.find h

theorem certifiedIndex_searchIndex {wq : (Fin n → Option (Fin 3)) → ℚ} {eps : ℚ}
    {Zapp : C → ℕ → (FiniteQubitConfiguration (Fin n) → ℚ) ×
      (FiniteQubitConfiguration (Fin n) → ℚ)}
    (h : ∃ k : ℕ, CertifiedIndex wq eps Zapp (certEnum n k)) :
    CertifiedIndex wq eps Zapp (certEnum n (searchIndex h)) :=
  Nat.find_spec h

/-- **The selected pair is a rational autonomous witness.** -/
theorem hard_searchIndex {wq : (Fin n → Option (Fin 3)) → ℚ} {eps : ℚ} (heps : 0 ≤ eps)
    {Z : C → (FiniteQubitConfiguration (Fin n) → ℂ)}
    {Zapp : C → ℕ → (FiniteQubitConfiguration (Fin n) → ℚ) ×
      (FiniteQubitConfiguration (Fin n) → ℚ)}
    (hZapp : ∀ κ mm, dist (eucVec (Z κ)) (eucVec (ratVecToC (Zapp κ mm)))
      ≤ 1 / ((mm : ℝ) + 1))
    (h : ∃ k : ℕ, CertifiedIndex wq eps Zapp (certEnum n k)) :
    0 < (certEnum n (searchIndex h)).2.2.2 ∧
      ((fun P => (((certEnum n (searchIndex h)).2.2.1 P : ℚ) : ℝ)),
          (((certEnum n (searchIndex h)).2.2.2 : ℚ) : ℝ))
        ∈ hardCircuitEvent (fun P => (wq P : ℝ)) (zeroProductState (Fin n))
          ((eps : ℚ) : ℝ) Z :=
  hard_of_certifiedIndex heps hZapp (certifiedIndex_searchIndex h)

end Search

end GaloisForLFunctions.HTGeometry

end
