import GaloisForLFunctions.RHTower.RankOnePolarizedExchangeCoherentKernel
import GaloisForLFunctions.HTGeometry.ExactnessFlagProvenanceTopology

/-!
# The off-horizon exchange complex and its landing criterion

The exchange defect at a calibrating pair `(2, n)` is square zero.  Its provenance flag is the
horizon flag `(0, ⊤)` when the character is trivial at `n`, and the off-horizon flag `(L, L)` on the
permanent conormal line otherwise.  Off the horizon the defect induces an isomorphism from the
transverse framed quotient onto the conormal error line, so the two-term exchange complex is acyclic
and every chain map into it vanishes on homology.

Consequently a homology-conservative landing forces the horizon at that degree, and landings over a
multiplicative generating set — in particular over the primes — force the trivial character.  The
assertion is one-way: triviality does not construct such a chain map.
-/

namespace RHTower

noncomputable section

open Matrix GaloisForLFunctions.HTGeometry

variable {k : Type*} [Field k]

/-! ## The square-zero exchange differential -/

/-- The exchange differential at a degree: the curvature at the calibrating pair `(2, n)`. -/
def exchangeDifferential (χ : ℕ+ →* kˣ) (n : ℕ+) : Matrix (Fin 2) (Fin 2) k :=
  exchangeCurvature χ 2 n

theorem exchangeDifferential_eq (χ : ℕ+ →* kˣ) (n : ℕ+) :
    exchangeDifferential χ n = ((χ 2 : k) * (1 - (χ n : k))) • exchangeE12 k :=
  exchangeCurvature_two χ n

/-- **The exchange differential is square zero.** -/
theorem exchangeDifferential_sq (χ : ℕ+ →* kˣ) (n : ℕ+) :
    exchangeDifferential χ n * exchangeDifferential χ n = 0 := by
  rw [exchangeDifferential_eq, Matrix.smul_mul, Matrix.mul_smul, exchangeE12_sq]
  simp

theorem exchangeDifferential_coeff_ne_zero {χ : ℕ+ →* kˣ} {n : ℕ+} (h : χ n ≠ 1) :
    (χ 2 : k) * (1 - (χ n : k)) ≠ 0 := by
  refine mul_ne_zero (Units.ne_zero (χ 2)) ?_
  intro hz
  exact h (Units.ext (by simp only [Units.val_one]; linear_combination -hz))

theorem ker_exchangeDifferential {χ : ℕ+ →* kˣ} {n : ℕ+} (h : χ n ≠ 1) :
    LinearMap.ker (Matrix.mulVecLin (exchangeDifferential χ n)) = permanentLine k := by
  rw [exchangeDifferential_eq]
  exact ker_smul_exchangeE12 (exchangeDifferential_coeff_ne_zero h)

theorem range_exchangeDifferential {χ : ℕ+ →* kˣ} {n : ℕ+} (h : χ n ≠ 1) :
    LinearMap.range (Matrix.mulVecLin (exchangeDifferential χ n)) = permanentLine k := by
  rw [exchangeDifferential_eq]
  exact range_smul_exchangeE12 (exchangeDifferential_coeff_ne_zero h)

theorem exchangeDifferential_eq_zero {χ : ℕ+ →* kˣ} {n : ℕ+} (h : χ n = 1) :
    exchangeDifferential χ n = 0 := by
  rw [exchangeDifferential_eq, h]
  simp

/-! ## The provenance flag of the exchange differential -/

theorem range_le_ker_exchangeDifferential (χ : ℕ+ →* kˣ) (n : ℕ+) :
    LinearMap.range (Matrix.mulVecLin (exchangeDifferential χ n)) ≤
      LinearMap.ker (Matrix.mulVecLin (exchangeDifferential χ n)) := by
  rintro w ⟨v, rfl⟩
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
    Matrix.mulVec_mulVec, exchangeDifferential_sq, Matrix.zero_mulVec]

/-- The provenance flag of the exchange differential: its image inside its kernel. -/
def exchangeFlag (χ : ℕ+ →* kˣ) (n : ℕ+) : ExFlag k (Fin 2 → k) :=
  ⟨LinearMap.range (Matrix.mulVecLin (exchangeDifferential χ n)),
    LinearMap.ker (Matrix.mulVecLin (exchangeDifferential χ n)),
    range_le_ker_exchangeDifferential χ n⟩

/-- **On the horizon the exchange flag is the fully surviving flag.** -/
theorem exchangeFlag_of_eq_one {χ : ℕ+ →* kˣ} {n : ℕ+} (h : χ n = 1) :
    exchangeFlag χ n = ⟨⊥, ⊤, le_top⟩ := by
  refine ExFlag.ext ?_ ?_ <;>
    simp [exchangeFlag, exchangeDifferential_eq_zero h]

/-- **Off the horizon the exchange flag is the permanent conormal line twice over.** -/
theorem exchangeFlag_of_ne_one {χ : ℕ+ →* kˣ} {n : ℕ+} (h : χ n ≠ 1) :
    exchangeFlag χ n = ⟨permanentLine k, permanentLine k, le_rfl⟩ := by
  refine ExFlag.ext ?_ ?_
  · exact range_exchangeDifferential h
  · exact ker_exchangeDifferential h

theorem subsingleton_quotient_of_eq_top {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {p : Submodule R M} (h : p = ⊤) : Subsingleton (M ⧸ p) := by
  subst h
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [Submodule.Quotient.eq]
  trivial

/-- **Off the horizon the exchange homology vanishes.** -/
theorem subsingleton_exchangeHomology {χ : ℕ+ →* kˣ} {n : ℕ+} (h : χ n ≠ 1) :
    Subsingleton (exchangeFlag χ n).homology := by
  rw [exchangeFlag_of_ne_one h]
  refine subsingleton_quotient_of_eq_top (eq_top_iff.2 fun x _ => ?_)
  exact x.2

/-- **On the horizon the exchange homology is the whole frame.** -/
noncomputable def exchangeHomologyEquiv {χ : ℕ+ →* kˣ} {n : ℕ+} (h : χ n = 1) :
    (exchangeFlag χ n).homology ≃ₗ[k] (Fin 2 → k) := by
  rw [exchangeFlag_of_eq_one h]
  exact (Submodule.quotEquivOfEqBot _ (by simp)).trans Submodule.topEquiv

/-! ## The off-horizon transverse contraction -/

theorem exchangeDifferential_mulVec_mem (χ : ℕ+ →* kˣ) (n : ℕ+) (v : Fin 2 → k) :
    Matrix.mulVec (exchangeDifferential χ n) v ∈ permanentLine k := by
  rw [exchangeDifferential_eq, Matrix.smul_mulVec, exchangeE12_mulVec, mem_permanentLine_iff]
  simp

theorem permanentLine_le_ker (χ : ℕ+ →* kˣ) (n : ℕ+) :
    permanentLine k ≤
      LinearMap.ker (((Matrix.mulVecLin (exchangeDifferential χ n)).codRestrict
        (permanentLine k) (exchangeDifferential_mulVec_mem χ n))) := by
  intro v hv
  rw [LinearMap.mem_ker]
  ext
  rw [LinearMap.codRestrict_apply, Matrix.mulVecLin_apply, exchangeDifferential_eq,
    Matrix.smul_mulVec, exchangeE12_mulVec, mem_permanentLine_iff.1 hv]
  simp

/-- The differential induced on the transverse framed quotient. -/
def transverseDifferential (χ : ℕ+ →* kˣ) (n : ℕ+) :
    ((Fin 2 → k) ⧸ permanentLine k) →ₗ[k] permanentLine k :=
  (permanentLine k).liftQ
    ((Matrix.mulVecLin (exchangeDifferential χ n)).codRestrict (permanentLine k)
      (exchangeDifferential_mulVec_mem χ n))
    (permanentLine_le_ker χ n)

@[simp] theorem transverseDifferential_mk (χ : ℕ+ →* kˣ) (n : ℕ+) (v : Fin 2 → k) :
    ((transverseDifferential χ n (Submodule.Quotient.mk v) : permanentLine k) : Fin 2 → k) =
      Matrix.mulVec (exchangeDifferential χ n) v := rfl

theorem injective_transverseDifferential {χ : ℕ+ →* kˣ} {n : ℕ+} (h : χ n ≠ 1) :
    Function.Injective (transverseDifferential χ n) := by
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker] at hx
  have hv : v ∈ LinearMap.ker (Matrix.mulVecLin (exchangeDifferential χ n)) := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, ← transverseDifferential_mk χ n v, hx]
    rfl
  rw [ker_exchangeDifferential h] at hv
  exact (Submodule.Quotient.mk_eq_zero _).2 hv

theorem surjective_transverseDifferential {χ : ℕ+ →* kˣ} {n : ℕ+} (h : χ n ≠ 1) :
    Function.Surjective (transverseDifferential χ n) := by
  intro w
  have hw : (w : Fin 2 → k) ∈ LinearMap.range (Matrix.mulVecLin (exchangeDifferential χ n)) := by
    rw [range_exchangeDifferential h]
    exact w.2
  obtain ⟨v, hv⟩ := hw
  refine ⟨Submodule.Quotient.mk v, Subtype.ext ?_⟩
  rw [transverseDifferential_mk]
  rw [Matrix.mulVecLin_apply] at hv
  exact hv

/-- **Off the horizon the differential contracts the transverse framed quotient isomorphically onto
the conormal error line.** -/
noncomputable def transverseEquiv {χ : ℕ+ →* kˣ} {n : ℕ+} (h : χ n ≠ 1) :
    ((Fin 2 → k) ⧸ permanentLine k) ≃ₗ[k] permanentLine k :=
  LinearEquiv.ofBijective (transverseDifferential χ n)
    ⟨injective_transverseDifferential h, surjective_transverseDifferential h⟩

/-! ## The homology-conservative landing criterion -/

section Landing

variable {B₁ B₀ : Type*} [AddCommGroup B₁] [Module k B₁] [AddCommGroup B₀] [Module k B₀]
variable {χ : ℕ+ →* kˣ} {n : ℕ+} {dB : B₁ →ₗ[k] B₀}
variable {f₁ : B₁ →ₗ[k] ((Fin 2 → k) ⧸ permanentLine k)} {f₀ : B₀ →ₗ[k] permanentLine k}

/-- Degree-one induced map on homology of a chain map into the exchange complex. -/
def landingH1 (hcomm : (transverseDifferential χ n).comp f₁ = f₀.comp dB) :
    LinearMap.ker dB →ₗ[k] LinearMap.ker (transverseDifferential χ n) :=
  (f₁.domRestrict (LinearMap.ker dB)).codRestrict _ (by
    intro x
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply,
      ← LinearMap.comp_apply, hcomm, LinearMap.comp_apply,
      (LinearMap.mem_ker.1 x.2), map_zero])

/-- Degree-zero induced map on homology of a chain map into the exchange complex. -/
def landingH0 (hcomm : (transverseDifferential χ n).comp f₁ = f₀.comp dB) :
    (B₀ ⧸ LinearMap.range dB) →ₗ[k]
      (permanentLine k ⧸ LinearMap.range (transverseDifferential χ n)) :=
  Submodule.mapQ _ _ f₀ (by
    rintro y ⟨x, rfl⟩
    rw [Submodule.mem_comap, ← LinearMap.comp_apply, ← hcomm, LinearMap.comp_apply]
    exact LinearMap.mem_range_self _ _)

/-- **Off the horizon every chain map into the exchange complex vanishes on degree-one
homology.** -/
theorem landingH1_eq_zero (hcomm : (transverseDifferential χ n).comp f₁ = f₀.comp dB)
    (h : χ n ≠ 1) : landingH1 hcomm = 0 := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  have hmem := (landingH1 hcomm x).2
  rw [LinearMap.ker_eq_bot.2 (injective_transverseDifferential h)] at hmem
  simpa using hmem

/-- **Off the horizon every chain map into the exchange complex vanishes on degree-zero
homology.** -/
theorem landingH0_eq_zero (hcomm : (transverseDifferential χ n).comp f₁ = f₀.comp dB)
    (h : χ n ≠ 1) : landingH0 hcomm = 0 := by
  have htop : LinearMap.range (transverseDifferential χ n) = ⊤ :=
    LinearMap.range_eq_top.2 (surjective_transverseDifferential h)
  have hsub := subsingleton_quotient_of_eq_top htop
  exact LinearMap.ext fun x => Subsingleton.elim _ _

/-- **A homology-conservative landing forces the horizon at that degree.** -/
theorem eq_one_of_landing_ne_zero (hcomm : (transverseDifferential χ n).comp f₁ = f₀.comp dB)
    (h : landingH1 hcomm ≠ 0 ∨ landingH0 hcomm ≠ 0) : χ n = 1 := by
  by_contra hne
  rcases h with h | h
  · exact h (landingH1_eq_zero hcomm hne)
  · exact h (landingH0_eq_zero hcomm hne)

end Landing

/-! ## Landings over a generating set -/

/-- A character trivial on a multiplicative generating set is trivial. -/
theorem eq_one_of_forall_mem_closure {χ : ℕ+ →* kˣ} {S : Set ℕ+}
    (hS : Submonoid.closure S = ⊤) (h : ∀ n ∈ S, χ n = 1) : χ = 1 := by
  refine MonoidHom.ext fun n => ?_
  have hmem : n ∈ Submonoid.closure S := by rw [hS]; trivial
  induction hmem using Submonoid.closure_induction with
  | mem x hx => exact h x hx
  | one => exact map_one χ
  | mul x y _ _ hx hy => rw [map_mul, hx, hy, one_mul]

/-- **A character trivial at every prime degree is trivial.** -/
theorem eq_one_of_forall_prime {χ : ℕ+ →* kˣ}
    (hp : ∀ p : ℕ+, Nat.Prime (p : ℕ) → χ p = 1) : χ = 1 := by
  have key : ∀ N : ℕ, ∀ n : ℕ+, (n : ℕ) = N → χ n = 1 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro n hn
      by_cases h1 : (n : ℕ) = 1
      · have hn1 : n = 1 := PNat.coe_injective (by rw [h1]; rfl)
        rw [hn1, map_one]
      · have hfac : Nat.Prime (n : ℕ).minFac := Nat.minFac_prime h1
        obtain ⟨q, hq⟩ := Nat.minFac_dvd (n : ℕ)
        have hqpos : 0 < q := by
          rcases Nat.eq_zero_or_pos q with rfl | hpos
          · rw [Nat.mul_zero] at hq
            exact absurd hq n.ne_zero
          · exact hpos
        have hPQ : n = (⟨(n : ℕ).minFac, hfac.pos⟩ : ℕ+) * ⟨q, hqpos⟩ :=
          PNat.coe_injective (by simpa [PNat.mul_coe] using hq)
        have h2q : 2 * q ≤ (n : ℕ) := by
          calc 2 * q ≤ (n : ℕ).minFac * q := Nat.mul_le_mul_right q hfac.two_le
            _ = (n : ℕ) := hq.symm
        have hqlt : q < N := by
          rw [← hn]
          omega
        rw [hPQ, map_mul, hp _ hfac, ih q hqlt ⟨q, hqpos⟩ rfl, mul_one]
  exact MonoidHom.ext fun n => key (n : ℕ) n rfl

end

end RHTower
