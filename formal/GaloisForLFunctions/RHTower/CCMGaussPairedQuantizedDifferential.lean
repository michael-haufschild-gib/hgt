import GaloisForLFunctions.RHTower.CCMSoninEdgeTrace

/-!
# Gauss-paired quantized differentials transport incidence linearly through the trace

The logarithmic quantized differential `ω(U) = U⁻¹ [F, U]` of a unit is a crossed homomorphism:
`ω(UV) = V⁻¹ ω(U) V + ω(V)`.  Iterating over a finite factorization gives the exact conjugated
channel decomposition, and any conjugation-invariant additive functional turns it into a plain sum.

Passing to the additive quotient by conjugation coboundaries `v⁻¹ x v − x` makes `ω` an honest
homomorphism, so every finite factorization of the same unit defines the same class: the Gauss
splitting and the pairing of archimedean components with primes create no ambiguity at the cyclic
coinvariant level.

Nothing here uses `F² = 1` or self-adjointness; only the Leibniz rule for the commutator.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {R : Type*} [Ring R]

/-- The logarithmic quantized differential of a unit, `ω(U) = U⁻¹ [F, U]`. -/
def logQuantizedDifferential (F : R) (U : Rˣ) : R := (↑U⁻¹ : R) * opComm F (U : R)

@[simp] theorem logQuantizedDifferential_one (F : R) :
    logQuantizedDifferential F (1 : Rˣ) = 0 := by
  unfold logQuantizedDifferential opComm
  simp

/-- **Equation (8b).**  The crossed-homomorphism law of the logarithmic quantized differential. -/
theorem logQuantizedDifferential_mul (F : R) (U V : Rˣ) :
    logQuantizedDifferential F (U * V)
      = (↑V⁻¹ : R) * logQuantizedDifferential F U * (V : R)
        + logQuantizedDifferential F V := by
  have hinv : ((↑(U * V)⁻¹ : R)) = (↑V⁻¹ : R) * (↑U⁻¹ : R) := by
    rw [mul_inv_rev, Units.val_mul]
  have hU : (↑U⁻¹ : R) * (U : R) = 1 := U.inv_mul
  unfold logQuantizedDifferential
  rw [Units.val_mul, opComm_mul, hinv]
  calc (↑V⁻¹ : R) * (↑U⁻¹ : R) * (opComm F (U : R) * (V : R) + (U : R) * opComm F (V : R))
      = (↑V⁻¹ : R) * ((↑U⁻¹ : R) * opComm F (U : R)) * (V : R)
        + (↑V⁻¹ : R) * ((↑U⁻¹ : R) * (U : R)) * opComm F (V : R) := by noncomm_ring
    _ = (↑V⁻¹ : R) * ((↑U⁻¹ : R) * opComm F (U : R)) * (V : R)
        + (↑V⁻¹ : R) * opComm F (V : R) := by rw [hU, mul_one]

/-! ## The conjugated channel decomposition -/

/-- The conjugated channel decomposition of a finite factorization. -/
def channelSum (F : R) : List Rˣ → R
  | [] => 0
  | U :: L => (↑(L.prod)⁻¹ : R) * logQuantizedDifferential F U * ((L.prod : Rˣ) : R)
      + channelSum F L

/-- **Equations (4)–(5).**  The logarithmic quantized differential of a finite product is the sum of
its channels, each conjugated by the product of the later factors. -/
theorem logQuantizedDifferential_list_prod (F : R) (L : List Rˣ) :
    logQuantizedDifferential F L.prod = channelSum F L := by
  induction L with
  | nil => simp [channelSum]
  | cons U L ih =>
      rw [List.prod_cons, logQuantizedDifferential_mul, ih]
      rfl

/-- **Equation (7).**  Any conjugation-invariant additive functional turns the channel decomposition
into a plain sum over the factors. -/
theorem trace_logQuantizedDifferential_list_prod {A : Type*} [AddCommGroup A] (τ : R →+ A)
    (hτ : ∀ (v : Rˣ) (x : R), τ ((↑v⁻¹ : R) * x * (v : R)) = τ x)
    (F : R) (L : List Rˣ) :
    τ (logQuantizedDifferential F L.prod)
      = (L.map (fun U => τ (logQuantizedDifferential F U))).sum := by
  induction L with
  | nil => simp
  | cons U L ih =>
      rw [List.prod_cons, logQuantizedDifferential_mul, map_add, hτ, ih]
      simp

/-! ## Descent to the cyclic coinvariants -/

/-- The additive subgroup of conjugation coboundaries `v⁻¹ x v − x`. -/
def conjCoboundary (R : Type*) [Ring R] : AddSubgroup R :=
  AddSubgroup.closure {y : R | ∃ (v : Rˣ) (x : R), y = (↑v⁻¹ : R) * x * (v : R) - x}

/-- The cyclic coinvariants: the additive quotient by conjugation coboundaries. -/
abbrev CyclicCoinvariants (R : Type*) [Ring R] := R ⧸ conjCoboundary R

theorem conj_sub_mem_conjCoboundary (v : Rˣ) (x : R) :
    (↑v⁻¹ : R) * x * (v : R) - x ∈ conjCoboundary R :=
  AddSubgroup.subset_closure ⟨v, x, rfl⟩

/-- **Equation (8d).**  In the cyclic coinvariants the logarithmic quantized differential is an
honest additive homomorphism. -/
theorem coinv_logQuantizedDifferential_mul (F : R) (U V : Rˣ) :
    (QuotientAddGroup.mk' (conjCoboundary R)) (logQuantizedDifferential F (U * V))
      = (QuotientAddGroup.mk' (conjCoboundary R)) (logQuantizedDifferential F U)
        + (QuotientAddGroup.mk' (conjCoboundary R)) (logQuantizedDifferential F V) := by
  rw [logQuantizedDifferential_mul, map_add]
  congr 1
  rw [← sub_eq_zero, ← map_sub]
  exact (QuotientAddGroup.eq_zero_iff _).mpr
    (conj_sub_mem_conjCoboundary V (logQuantizedDifferential F U))

/-- The class of a finite factorization is the sum of the classes of its factors. -/
theorem coinv_logQuantizedDifferential_list_prod (F : R) (L : List Rˣ) :
    (QuotientAddGroup.mk' (conjCoboundary R)) (logQuantizedDifferential F L.prod)
      = (L.map (fun U =>
          (QuotientAddGroup.mk' (conjCoboundary R)) (logQuantizedDifferential F U))).sum := by
  induction L with
  | nil => simp
  | cons U L ih =>
      rw [List.prod_cons, coinv_logQuantizedDifferential_mul, ih]
      simp

/-- **Equation (8e).**  Two finite factorizations of the same unit have the same total class: the
Gauss splitting and the component/prime pairing create no ambiguity. -/
theorem coinv_sum_eq_of_prod_eq (F : R) (L L' : List Rˣ) (h : L.prod = L'.prod) :
    (L.map (fun U =>
        (QuotientAddGroup.mk' (conjCoboundary R)) (logQuantizedDifferential F U))).sum
      = (L'.map (fun U =>
        (QuotientAddGroup.mk' (conjCoboundary R)) (logQuantizedDifferential F U))).sum := by
  rw [← coinv_logQuantizedDifferential_list_prod, ← coinv_logQuantizedDifferential_list_prod, h]

/-! ## The Hardy reflection form -/

/-- **Equation (15).**  For the reflection `F = 2P − 1` the logarithmic quantized differential is
twice the conjugated projection defect. -/
theorem logQuantizedDifferential_reflection (P : R) (U : Rˣ) :
    logQuantizedDifferential (2 * P - 1) U = 2 * ((↑U⁻¹ : R) * P * (U : R) - P) := by
  have hU : (↑U⁻¹ : R) * (U : R) = 1 := U.inv_mul
  unfold logQuantizedDifferential opComm
  calc (↑U⁻¹ : R) * ((2 * P - 1) * (U : R) - (U : R) * (2 * P - 1))
      = 2 * ((↑U⁻¹ : R) * P * (U : R)) - 2 * ((↑U⁻¹ : R) * (U : R) * P) := by noncomm_ring
    _ = 2 * ((↑U⁻¹ : R) * P * (U : R) - P) := by rw [hU]; noncomm_ring

/-! ## The coefficient-state budget -/

/-- **Equation (19).**  A coefficient hull contained in the frequency module leaves no residual
state charge: the quotient is trivial. -/
theorem coefficientState_quotient_trivial {V Γ : Submodule ℚ ℝ} (h : V ≤ Γ) :
    Submodule.comap V.subtype Γ = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  simpa using h x.2

end

end GaloisForLFunctions.RHTower
