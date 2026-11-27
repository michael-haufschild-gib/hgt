import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Response
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Stationarity
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Probability
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdjacentShellTrace

/-! # The maximal strip for one prime comparison and the partition zeros -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity

open Real Set Finset

/-- Reliability on a domain specified by the magnitude of split damping. -/
def reliable (p q : Nat.Primes) (U : Set ℝ) := ∀ s : ℂ, |2*s.re-1|∈U →
    (accepts (packet p) q (2*s.re-1) ↔ ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x)

/-- The nonisometric return can be realized at a real parameter. Thus its
omission is necessary and sufficient, for an arbitrary damping domain. -/
theorem reliable_iff (p q : Nat.Primes) (U : Set ℝ) :
    reliable p q U ↔ log p.val/log q.val∉U := by
  let τ := log p.val/log q.val
  have pos : 0<τ := div_pos (log_pos_prime p) (log_pos_prime q)
  constructor
  · intro good member
    let s : ℂ := (((1+τ)/2 : ℝ) : ℂ)
    have d : 2*s.re-1=τ := by change 2*((1+τ)/2)-1=τ; ring
    have absd : |2*s.re-1|=τ := by rw [d,abs_of_pos pos]
    have hit := (packet_response p q (2*s.re-1)).mpr (Or.inr absd)
    have line := (split_isometric_iff s).mp ((good s (by rw [absd]; exact member)).mp hit)
    rw [line] at d
    linarith only [d,pos]
  · intro absent s member
    rw [packet_response,split_isometric_iff]
    have no : |2*s.re-1|≠τ := by
      intro eq
      apply absent
      change τ∈U
      rwa [←eq]
    rw [or_iff_left no]
    constructor <;> intro h <;> linarith only [h]

/-- The open band may reach the first false return exactly; the closed
band must end strictly before it. -/
theorem band_endpoints (p q : Nat.Primes) (w : ℝ) :
    (reliable p q (Iio w) ↔ w≤log p.val/log q.val) ∧
    (reliable p q (Iic w) ↔ w<log p.val/log q.val) := by
  constructor
  · rw [reliable_iff]
    change (¬log p.val/log q.val<w) ↔ _
    exact not_lt
  · rw [reliable_iff]
    change (¬log p.val/log q.val≤w) ↔ _
    exact not_le

/-- A single measurement is exact on the entire critical strip precisely
when its elementary prime does not exceed the calibration prime. -/
theorem strip_iff (p q : Nat.Primes) :
    (∀ s : OpenStrip, accepts (packet p) q (2*s.val.re-1) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s.val f x) ↔ q.val≤p.val := by
  have window (s : ℂ) : |2*s.re-1|<1 ↔ 0<s.re ∧ s.re<1 := by
    rw [abs_lt]
    constructor <;> rintro ⟨lo,hi⟩ <;> constructor <;> linarith only [lo,hi]
  have same : (∀ s : OpenStrip, accepts (packet p) q (2*s.val.re-1) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s.val f x) ↔ reliable p q (Iio 1) :=
    ⟨fun h s hs => h ⟨s,(window s).mp hs⟩,fun h s => h s.val ((window s.val).mpr s.property)⟩
  rw [same,(band_endpoints p q 1).1,le_div_iff₀ (log_pos_prime q),one_mul]
  have pos (r : Nat.Primes) : 0<(r.val : ℝ) := Nat.cast_pos.mpr r.property.pos
  exact (log_le_log_iff (pos q) (pos p)).trans Nat.cast_le

/-- Total states of the peak-minimizing preparation. In particular the
binary calibration uses thirty states and peak multiplicity three. -/
theorem state_count (p : Nat.Primes) : Fintype.card (States p)=6*(p.val^2+1) := by
  have size := packet_sum p (fun _ => (1 : ℕ))
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one,Nat.cast_id] at size
  change Fintype.card (States p)=p.val*6+threshold p*6 at size
  have pred : p.val-1+1=p.val := Nat.sub_add_cancel p.property.one_lt.le
  have ab : p.val*(p.val-1)+p.val=p.val^2 := by
    calc
      _ = p.val*(p.val-1+1) := by ring
      _ = _ := by rw [pred,pow_two]
  rw [size,threshold]
  omega

/-- For the same calibration and probe prime, a vanishing adjacent-shell
interference trace forces the finite Gibbs equality for every point in the
strip if and only if RH holds. -/
theorem rh_iff_trace_forces_reading (p : Nat.Primes) :
    RiemannHypothesis ↔ ∀ s : OpenStrip,
      ContinuousLinearMap.opTrace (adjacentOperator ⟨s.val,s.property.1⟩)=0 →
        accepts (packet p) p (2*s.val.re-1) := by
  have exactTest := (strip_iff p p).mpr (le_refl _)
  rw [rh_iff_trace_zero_forces_isometry]
  exact ⟨fun h s hz => (exactTest s).mpr (h s hz),fun h s hz => (exactTest s).mp (h s hz)⟩

/-- The identical finite comparison can be stated directly at zeta zeros. -/
theorem rh_iff_zeta_forces_reading (p : Nat.Primes) :
    RiemannHypothesis ↔ ∀ s : OpenStrip, riemannZeta s.val=0 → accepts (packet p) p (2*s.val.re-1) := by
  rw [rh_iff_trace_forces_reading p]
  exact ⟨fun h s hz => h s ((adjacentTrace_zero_iff s).mpr hz),fun h s hz => h s ((adjacentTrace_zero_iff s).mp hz)⟩

abbrev binary : Nat.Primes := ⟨2,Nat.prime_two⟩

/-- One normalized probability vector of thirty binary-mode states. -/
def binaryLaw (s : ℂ) := _root_.HTGeometry.finiteGibbsStateWeight (2*s.re-1) (primeModes binary (packet binary))

private theorem binary_reading (s : ℂ) : accepts (packet binary) binary (2*s.re-1) ↔
    (cofactorSum (binaryLaw s))^15=(∏ i, binaryLaw s i)^14 := by
  have size : Fintype.card (States binary)=2*(14+1) := state_count binary
  letI : Nonempty (States binary) := Fintype.card_pos_iff.mp (by omega)
  exact even_probability_law (binaryLaw s)
    (fun i => _root_.HTGeometry.finiteGibbsStateWeight_pos _ _ i)
    (_root_.HTGeometry.sum_finiteGibbsStateWeight_eq_one _ _) 14 size

/-- The unordered entries satisfy a single symmetric polynomial equation
exactly on the isometry line throughout the open critical strip. -/
theorem binary_polynomial_isometry (s : OpenStrip) :
    (cofactorSum (binaryLaw s.val))^15=(∏ i, binaryLaw s.val i)^14 ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s.val f x :=
  (binary_reading s.val).symm.trans ((strip_iff binary binary).mpr (le_refl _) s)

/-- RH asks whether every strip zero gives a binary Gibbs vector on
the explicit symmetric polynomial hypersurface. -/
theorem rh_iff_binary_polynomial :
    RiemannHypothesis ↔ ∀ s : OpenStrip, riemannZeta s.val=0 →
      (cofactorSum (binaryLaw s.val))^15=(∏ i, binaryLaw s.val i)^14 := by
  rw [rh_iff_zeta_forces_reading binary]
  exact ⟨fun h s hz => (binary_reading s.val).mp (h s hz),fun h s hz => (binary_reading s.val).mpr (h s hz)⟩

#print axioms binary_polynomial_isometry
#print axioms rh_iff_binary_polynomial
#print axioms reliable_iff
#print axioms band_endpoints
#print axioms strip_iff
#print axioms state_count
#print axioms rh_iff_trace_forces_reading
#print axioms rh_iff_zeta_forces_reading

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity
