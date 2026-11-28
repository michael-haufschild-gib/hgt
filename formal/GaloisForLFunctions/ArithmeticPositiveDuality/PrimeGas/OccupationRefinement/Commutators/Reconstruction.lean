import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators.Hamiltonian
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators.Response
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.Tomography

/-! # Canonical commutation, prime composition and the thermal partition function -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators

open CoassociativeSplitting ModeCapacities CoherentRay UniversalResponse

theorem general_counts (A : Response) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v)
    (p : Nat.Primes) (k : ℕ) : ‖ladder (routing A.val u v) p k‖ ^ 2 = (k:ℝ) := by
  cases k with
  | zero => simp [ladder]
  | succ k =>
    have mem : 1/((k+1:ℕ):ℝ) ∈ Shares := ⟨one_div_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos k)),
      (div_le_one (Nat.cast_pos.mpr (Nat.succ_pos k))).mpr (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))⟩
    rw [response_ladder A hu hv, norm_inv, inv_pow, A.property.2 _ mem, one_div, inv_inv]

theorem general_canonical (A : Response) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v)
    (p : Nat.Primes) : bracket (lower (routing A.val u v) p) (raise (routing A.val u v) p) = LinearMap.id :=
  (bracket_iff_counts _ p).mpr (general_counts A hu hv p)

theorem commutator_response_iff (A : ℝ → ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v)
    (p : Nat.Primes) :
    sequential A ∧ bounded A ∧ bracket (lower (routing A u v) p) (raise (routing A u v) p) = LinearMap.id ↔
      sequential A ∧ conserving A := by
  constructor
  · rintro ⟨seq,bound,h⟩
    apply (square_response_iff A hu hv p).mp
    exact ⟨seq,bound,by simpa only [Nat.cast_ofNat] using (bracket_iff_counts _ p).mp h 2⟩
  · intro h
    let R : Response := ⟨A,(response_iff A).mpr h⟩
    exact ⟨h.1,((born_iff A).mpr R.property).2.1,general_canonical R hu hv p⟩

/-- A single square-shell reading detects canonical commutation even
with unknown shell gain and independent complex gains on the two outputs. -/
theorem detector_iff (D : Detector) (s : ℂ) :
    ‖(readings (detected D s)).1‖ = 2 ↔
      bracket (lower (kernel s D.u.val D.v.val) D.prime)
        (raise (kernel s D.u.val D.v.val) D.prime) = LinearMap.id := by
  let K := kernel s D.u.val D.v.val
  have signal : power s 4 = (power s 2)^2 := by
    simpa only [show (2:ℝ)^2=4 by norm_num] using power_nat s (by norm_num : 0<(2:ℝ)) 2
  have two : ladder K D.prime 2 = power s 2 := measured s D.u.property D.v.property D.prime 1
  have one : ladder K D.prime 1 = 1 := by
    simpa only [Nat.zero_add, Nat.cast_one, unit_power] using measured s D.u.property D.v.property D.prime 0
  rw [coherent_readings,canonical_iff s D.u.property D.v.property D.prime,
    ← first_increment_iff s D.u.property D.v.property D.prime]
  change ‖power s 4‖ = 2 ↔ ‖ladder K D.prime 2‖^2 - ‖ladder K D.prime 1‖^2 = 1
  rw [signal,norm_pow,two,one,norm_one,one_pow]
  constructor <;> intro h <;> linarith only [h]

/-- One mode tests the entire quantum algebra. On its canonical line all
integer energies are sums of the measured number operators; the full Gibbs
operator has zeta trace in the trace half-plane. -/
theorem quantum_algebra (s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (p : Nat.Primes) :
    let K := kernel s u v
    (bracket (lower K p) (raise K p) = LinearMap.id ↔ isometric K) ∧
    (bracket (lower K p) (raise K p) = LinearMap.id ↔ s.re=1/2) ∧
    (s.re=1/2 → ∀ f : Core, ∃ g : hamiltonian.domain, g.val=embed f ∧
      hamiltonian g=embed (modeEnergy K (activeModes f) f)) ∧
    (∀ a b : Occupation, label (a+b)=label a*label b) ∧
    (∀ a b : ℕ+, energy (a*b)=energy a+energy b) ∧
    ∀ z : TracePoint, ContinuousLinearMap.opTrace (gibbsOperator z)=riemannZeta z.val :=
  ⟨canonical_iff_isometric s hu hv p,canonical_iff s hu hv p,sum_number s hu hv,
    label_add,energy_mul,partition_eq_zeta⟩

#print axioms general_canonical
#print axioms commutator_response_iff
#print axioms detector_iff
#print axioms quantum_algebra

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators
