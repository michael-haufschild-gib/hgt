import GaloisForLFunctions.HTGeometry.EndpointChirpTerm
import GaloisForLFunctions.HTGeometry.EndpointJetSum

/-!
# The chirp data attached to an endpoint pair

An endpoint pair `(j, q)` — jet index `j`, offset `q < R` — carries three numbers once the
coefficient degree is written as `N = M + R`:

* the forward shift `u = R − q + j ≥ 1`,
* the real exponent `ρ = j + (Re α)·u`,
* the integer frequency `u`.

The pairs are separated by these: equal exponents together with equal shifts force equal pairs.
That is why the surviving layer of the chirp sum is a trigonometric polynomial with *distinct*
frequencies, and it is the only place where `q < R` is used.

The endpoint term of the pair is exactly the chirp with this data, times a factor tending to one.
-/

open MvPolynomial PowerSeries Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The data -/

/-- The forward shift attached to an endpoint pair. -/
def endpointShift {m R : ℕ} (jq : Fin (m + 1) × Fin R) : ℕ := R - (jq.2 : ℕ) + (jq.1 : ℕ)

theorem one_le_endpointShift {m R : ℕ} (jq : Fin (m + 1) × Fin R) : 1 ≤ endpointShift jq := by
  have hq : (jq.2 : ℕ) < R := jq.2.isLt
  rw [endpointShift]
  omega

/-- The real exponent attached to an endpoint pair. -/
def endpointExponent (α : ℂ) {m R : ℕ} (jq : Fin (m + 1) × Fin R) : ℝ :=
  ((jq.1 : ℕ) : ℝ) + α.re * ((endpointShift jq : ℕ) : ℝ)

/-- The integer frequency attached to an endpoint pair. -/
def endpointFreq {m R : ℕ} (jq : Fin (m + 1) × Fin R) : ℤ := (endpointShift jq : ℤ)

/-- The chirp coefficient attached to an endpoint pair. -/
def endpointCoeff (α Λ : ℂ) {m R : ℕ} (cc : Fin (m + 1) → ℕ → ℂ)
    (jq : Fin (m + 1) × Fin R) : ℂ :=
  cc jq.1 (jq.2 : ℕ) * Λ ^ endpointShift jq * α ^ (α * ((endpointShift jq : ℕ) : ℂ))

/-! ## Separation -/

/-- **The endpoint data separates the pairs.** -/
theorem endpoint_pair_separation {α : ℂ} {m R : ℕ} (jq₁ jq₂ : Fin (m + 1) × Fin R)
    (hρ : endpointExponent α jq₁ = endpointExponent α jq₂)
    (hk : endpointFreq jq₁ = endpointFreq jq₂) : jq₁ = jq₂ := by
  have hu : endpointShift jq₁ = endpointShift jq₂ := by
    have := hk
    rw [endpointFreq, endpointFreq] at this
    exact_mod_cast this
  have huR : ((endpointShift jq₁ : ℕ) : ℝ) = ((endpointShift jq₂ : ℕ) : ℝ) := by
    exact_mod_cast hu
  have hjR : ((jq₁.1 : ℕ) : ℝ) = ((jq₂.1 : ℕ) : ℝ) := by
    rw [endpointExponent, endpointExponent, huR] at hρ
    linarith
  have hj : (jq₁.1 : ℕ) = (jq₂.1 : ℕ) := by exact_mod_cast hjR
  have hq₁ : (jq₁.2 : ℕ) < R := jq₁.2.isLt
  have hq₂ : (jq₂.2 : ℕ) < R := jq₂.2.isLt
  have hq : (jq₁.2 : ℕ) = (jq₂.2 : ℕ) := by
    rw [endpointShift, endpointShift] at hu
    omega
  exact Prod.ext (Fin.ext hj) (Fin.ext hq)

/-! ## The term -/

variable {a : ℕ → ℂ} {α Λ Cc : ℂ} {c : ℝ}

/-- **The endpoint term of a pair is its chirp.** -/
theorem endpoint_pair_term_eq_chirp (hyp : FactorialSlope a α Λ Cc c) {m R : ℕ}
    (cc : Fin (m + 1) → ℕ → ℂ) (jq : Fin (m + 1) × Fin R)
    {M : ℕ} (hM : 1 ≤ M) (haM : a M ≠ 0) :
    cc jq.1 (jq.2 : ℕ)
        * (((((M + R) - (jq.2 : ℕ) + (jq.1 : ℕ)).descFactorial (jq.1 : ℕ) : ℕ) : ℂ)
          * a ((M + R) - (jq.2 : ℕ) + (jq.1 : ℕ))) / a M
      = chirpTerm α.im (endpointExponent α jq) (endpointFreq jq)
          (endpointCoeff α Λ cc jq) (Real.log M)
        * slopeShiftDefect a α Λ (endpointShift jq) (jq.1 : ℕ) M := by
  have hq : (jq.2 : ℕ) < R := jq.2.isLt
  have hidx : (M + R) - (jq.2 : ℕ) + (jq.1 : ℕ) = M + endpointShift jq := by
    rw [endpointShift]
    omega
  rw [hidx]
  have hbase := endpoint_term_eq_chirp hyp (endpointShift jq) (jq.1 : ℕ)
    (cc jq.1 (jq.2 : ℕ)) hM haM
  rw [hbase, endpointExponent, endpointFreq, endpointCoeff]

/-! ## Indexing the endpoint pairs -/

/-- The endpoint double sum is a sum over the finite type of pairs. -/
theorem sum_endpoint_pairs {m R : ℕ} (f : Fin (m + 1) → ℕ → ℂ) :
    (∑ jq : Fin (m + 1) × Fin R, f jq.1 (jq.2 : ℕ))
      = ∑ j : Fin (m + 1), ∑ q ∈ Finset.range R, f j q := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun j _ => Fin.sum_univ_eq_sum_range (fun q => f j q) R

/-- The exponent of an endpoint pair is at least the shift scaled by the ray abscissa. -/
theorem le_endpointExponent {α : ℂ} {m R : ℕ}
    (jq : Fin (m + 1) × Fin R) :
    α.re * ((endpointShift jq : ℕ) : ℝ) ≤ endpointExponent α jq := by
  rw [endpointExponent]
  have : (0 : ℝ) ≤ ((jq.1 : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

/-- The shift of a pair with offset `q` is at least `R − q`. -/
theorem sub_le_endpointShift {m R : ℕ} (jq : Fin (m + 1) × Fin R) :
    R - (jq.2 : ℕ) ≤ endpointShift jq := by
  rw [endpointShift]
  omega

end

end GaloisForLFunctions.HTGeometry
