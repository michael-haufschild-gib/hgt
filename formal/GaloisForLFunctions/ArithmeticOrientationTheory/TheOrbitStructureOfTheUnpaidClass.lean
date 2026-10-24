import GaloisForLFunctions.ArithmeticOrientationTheory.NonvanishingOnTheHalfPlaneDoesNotMakeAUnit
import GaloisForLFunctions.ArithmeticOrientationTheory.TheEvenFlipCreatesAnObstructionAtThePole
import GaloisForLFunctions.ArithmeticOrientationTheory.TheEvenFlipOfTheMoebiusReceiverKeepsItsObstructions
import GaloisForLFunctions.ArithmeticOrientationTheory.TheMoebiusReceiverCountsItsOffLineZeros

/-!
# The orbit structure of the unpaid class

Under Dirichlet convolution, the critical Wiener monoid `CriticalWiener` (`𝒲_{1/2}`) and its unit
group `IsWienerUnit` (`𝒲_{1/2}^×`) act on arithmetic weights `c : ℕ → ℝ` with summable mean
`∑_d |c(d)/d| < ∞`. Both the paid class `ReceiverBounded` and the unpaid class `¬ ReceiverBounded`
are unions of unit orbits (`UnitsOfTheWienerMonoidPreservePayment`), while the paid class is a
forward-invariant ideal under the full monoid (`TheCriticalWienerMonoid`).

This module resolves Open Problem 5 of Arithmetic Orientation Theory by classifying the orbit
structure of the unpaid class under `IsWienerUnit` and `CriticalWiener`:

1. **The unit-orbit equivalence `WienerUnitOrbit` and monoid-orbit preorder `WienerMonoidOrbit` (§1):**
   - `WienerUnitOrbit c₁ c₂` (`∃ u, IsWienerUnit u ∧ ∀ n ≠ 0, c₂ n = (u ⋆ c₁) n`) is an equivalence
     relation (`equivalence_wienerUnitOrbit`), and `WienerMonoidOrbit c₁ c₂`
     (`∃ k, CriticalWiener k ∧ ∀ n ≠ 0, c₂ n = (k ⋆ c₁) n`) is a preorder (`wienerMonoidOrbit_refl`,
     `wienerMonoidOrbit_trans`) whose symmetric core contains `WienerUnitOrbit`.
   - Along any unit orbit `WienerUnitOrbit c₁ c₂`, payment (`receiverBounded_iff_of_wienerUnitOrbit`),
     the repairing ideal `paidIdeal` (`paidIdeal_eq_of_wienerUnitOrbit`), the obstruction hull
     `obstructionHull` (`obstructionHull_eq_of_wienerUnitOrbit`), and the quotient codimension
     `Module.rank` / `Module.finrank` (`rank_quotient_paidIdeal_eq_of_wienerUnitOrbit`,
     `finrank_quotient_paidIdeal_eq_of_wienerUnitOrbit`) are all exact invariants.
   - Along any monoid transition `WienerMonoidOrbit c₁ c₂`, the repairing ideal ascends
     (`paidIdeal c₁ hc₁ ≤ paidIdeal c₂ hc₂`, `paidIdeal_le_of_wienerMonoidOrbit`), the obstruction
     hull descends (`obstructionHull c₂ hc₂ ⊆ obstructionHull c₁ hc₁`,
     `obstructionHull_subset_of_wienerMonoidOrbit`), the quotient rank descends
     (`Module.rank ℂ (𝒲_{1/2} ⧸ paidIdeal c₂ hc₂) ≤ Module.rank ℂ (𝒲_{1/2} ⧸ paidIdeal c₁ hc₁)`,
     `rank_quotient_paidIdeal_le_of_wienerMonoidOrbit`), and the paid class is the unique forward
     sink (`receiverBounded_of_wienerMonoidOrbit`).

2. **Sharp stabilizer–annihilator dichotomy on principal and conjugate-pair orbits (§2):**
   - For any unpaid weight `c` whose repairing ideal is the maximal ideal of a Bohr point `ω₀`
     (`paidIdeal c hc = RingHom.ker (bohrCharacter (1 / 2) ω₀)`, including the smooth power `d^{−ε}`
     and every unpaid `k₀ ⋆ oddSqfWeight ε`), the monoid orbit `{k ⋆ c : CriticalWiener k}` splits
     into **exactly two** ideal classes (`paidIdeal_conv_dichotomy_of_eq_ker`):
     - the *annihilator* `bohrEval (1/2) (realFn k) ω₀ = 0`, where `k ⋆ c` is paid (`paidIdeal = ⊤`,
       `obstructionHull = ∅`, `finrank = 0`), and
     - the *stabilizer* `bohrEval (1/2) (realFn k) ω₀ ≠ 0`, where `k ⋆ c` remains unpaid with the
       **identical** repairing ideal `paidIdeal (k ⋆ c) = paidIdeal c`, **identical** obstruction
       hull `obstructionHull (k ⋆ c) = obstructionHull c`, and codimension `finrank = 1`.
   - For the oscillating probe `oscillatingSmoothPower ε t` (`0 < ε < 1/2`, `t ≠ 0`, `ζ(ρ) ≠ 0` at
     `ρ = 1 − ε + it`), real kernels satisfy `complexPoleValue k ρ̄ = conj (complexPoleValue k ρ)`
     and therefore cannot separate `ρ` from `ρ̄`: for every real `CriticalWiener k`, `k ⋆ c` has
     codimension **either `2`** (when `complexPoleValue k ρ ≠ 0`, preserving `paidIdeal` and
     `obstructionHull` identically) **or `0`** (when `complexPoleValue k ρ = 0`, paid); no real
     convolution ever lands at codimension `1` (`paidIdeal_oscillating_conv_dichotomy`).

3. **Dirichlet cancellation and infinite irreversible chains inside a single obstruction hull (§3):**
   - For any weight `c : ℕ → ℝ` normalized at `1` (`c 1 ≠ 0`), Dirichlet convolution with `c` is
     injective away from `0` (`dirichletConv_right_inj_of_apply_one_ne_zero`). Consequently, for
     every critical Wiener kernel `k`:
     `WienerMonoidOrbit (k ⋆ c) c ↔ IsWienerUnit k` (`wienerMonoidOrbit_conv_self_iff`) and
     `WienerUnitOrbit c (k ⋆ c) ↔ IsWienerUnit k` (`wienerUnitOrbit_conv_self_iff`).
   - Applying this to the real three-term kernel `realThreeTermKernel = δ₁ − ½√2 δ₂ + ½√3 δ₃`
     (`NonvanishingOnTheHalfPlaneDoesNotMakeAUnit`), which has no zero on `Re s ≥ ½` yet is not a
     unit, the iterated convolutions `iterThreeTermConv m (d^{−ε})` (`m : ℕ`, `0 < ε < 1/2`) form
     an **infinite strictly descending chain** in `WienerMonoidOrbit` whose members all share the
     **exact same** repairing ideal `RingHom.ker (bohrCharacter (1/2) (polePoint ε hε2.le))`, the
     **exact same** obstruction hull `{polePoint ε}`, and codimension `1`, while lying in pairwise
     distinct `WienerUnitOrbit` classes (`iterThreeTermConv_smoothPower_chain`).

4. **One-way orientation transitions and incomparable unpaid cones (§4):**
   - On the damped Möbius weight `pmPowerDampedRealWeight ε = (δ₁ − 2^{−ε} δ₂) ⋆ moebiusOddPart ε`
     (`0 < ε ≤ 1/2`), the 2-local factor `δ₁ − 2^{−ε} δ₂` is a unit (`2^{−ε} < 1 < √2`), whereas
     the flipped 2-local factor `(1 − 2^{−ε}) δ₁ + 2^{−ε} δ₂` is not a unit
     (`not_isWienerUnit_flipKernel_moebius`). Hence the even flip is an **irreversible monoid
     transition** on the Möbius receiver: `WienerMonoidOrbit (μ d^{−ε}) (evenFlip (μ d^{−ε}))` holds,
     while `¬ WienerMonoidOrbit (evenFlip (μ d^{−ε})) (μ d^{−ε})` and
     `¬ WienerUnitOrbit (μ d^{−ε}) (evenFlip (μ d^{−ε}))` (`moebius_evenFlip_oneWay_orbit`).
   - Unpaid weights with non-nested obstruction hulls — such as `d^{−ε₁}` and `d^{−ε₂}` for
     `ε₁ ≠ ε₂`, or `d^{−ε}` and `oscillatingSmoothPower ε t` (`t ≠ 0`, `ζ(1 − ε + it) ≠ 0`) — lie
     in strictly incomparable `WienerMonoidOrbit` cones (`not_wienerMonoidOrbit_smoothPower_of_ne`,
     `not_wienerMonoidOrbit_smoothPower_oscillating`).
-/

open Finset ArithmeticFunction LSeries Complex

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open TransHorizonIncidenceMechanics WienerAlgebraAt BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ### 1. The unit-orbit equivalence `WienerUnitOrbit` and monoid-orbit preorder `WienerMonoidOrbit` -/

/-- `c₂` lies in the unit orbit of `c₁` under the critical Wiener unit group `IsWienerUnit`
away from `0`. -/
def WienerUnitOrbit (c₁ c₂ : ℕ → ℝ) : Prop :=
  ∃ u : ℕ → ℝ, IsWienerUnit u ∧ ∀ n : ℕ, n ≠ 0 → c₂ n = RHTower.dirichletConv u c₁ n

/-- `c₂` lies in the monoid orbit of `c₁` under the critical Wiener monoid `CriticalWiener`
away from `0`. -/
def WienerMonoidOrbit (c₁ c₂ : ℕ → ℝ) : Prop :=
  ∃ k : ℕ → ℝ, CriticalWiener k ∧ ∀ n : ℕ, n ≠ 0 → c₂ n = RHTower.dirichletConv k c₁ n

theorem isWienerUnit_congr {a b : ℕ → ℝ} (h : ∀ n, n ≠ 0 → a n = b n) :
    IsWienerUnit a ↔ IsWienerUnit b := by
  unfold IsWienerUnit
  rw [criticalWiener_congr h]
  refine and_congr_right fun _ => exists_congr fun g => and_congr_right fun _ =>
    forall_congr' fun n => imp_congr_right fun _ => ?_
  rw [dirichletConv_congr h (fun _ _ => rfl) n]

theorem isWienerUnit_unitKernel : IsWienerUnit unitKernel :=
  ⟨criticalWiener_unitKernel, unitKernel, criticalWiener_unitKernel,
    fun _ hn => dirichletConv_unitKernel unitKernel hn⟩

theorem IsWienerUnit.dirichletConv {a b : ℕ → ℝ} (ha : IsWienerUnit a) (hb : IsWienerUnit b) :
    IsWienerUnit (RHTower.dirichletConv a b) := by
  obtain ⟨ha1, g, hg, hag⟩ := ha
  obtain ⟨hb1, h, hh, hbh⟩ := hb
  refine ⟨criticalWiener_dirichletConv ha1 hb1, RHTower.dirichletConv g h,
    criticalWiener_dirichletConv hg hh, fun n hn => ?_⟩
  have h1 : RHTower.dirichletConv (RHTower.dirichletConv a b) (RHTower.dirichletConv g h) n =
      RHTower.dirichletConv (RHTower.dirichletConv a g) (RHTower.dirichletConv b h) n := by
    rw [dirichletConv_assoc, ← dirichletConv_assoc b g h, dirichletConv_comm b g,
      dirichletConv_assoc g b h, ← dirichletConv_assoc]
  rw [h1, dirichletConv_congr hag hbh n, dirichletConv_unitKernel unitKernel hn]

theorem wienerUnitOrbit_refl (c : ℕ → ℝ) : WienerUnitOrbit c c :=
  ⟨unitKernel, isWienerUnit_unitKernel, fun _ hn => (dirichletConv_unitKernel c hn).symm⟩

theorem wienerUnitOrbit_symm {c₁ c₂ : ℕ → ℝ} (h : WienerUnitOrbit c₁ c₂) :
    WienerUnitOrbit c₂ c₁ := by
  obtain ⟨u, ⟨hu, v, hv, huv⟩, hc⟩ := h
  have hvu : ∀ n, n ≠ 0 → RHTower.dirichletConv v u n = unitKernel n := fun n hn => by
    rw [dirichletConv_comm]; exact huv n hn
  refine ⟨v, ⟨hv, u, hu, hvu⟩, fun n hn => ?_⟩
  rw [dirichletConv_congr (fun _ _ => rfl) hc n, ← dirichletConv_assoc,
    dirichletConv_congr hvu (fun _ _ => rfl) n, dirichletConv_unitKernel c₁ hn]

theorem wienerUnitOrbit_trans {c₁ c₂ c₃ : ℕ → ℝ}
    (h₁₂ : WienerUnitOrbit c₁ c₂) (h₂₃ : WienerUnitOrbit c₂ c₃) :
    WienerUnitOrbit c₁ c₃ := by
  obtain ⟨u₁, hu₁, hc₁₂⟩ := h₁₂
  obtain ⟨u₂, hu₂, hc₂₃⟩ := h₂₃
  refine ⟨RHTower.dirichletConv u₂ u₁, hu₂.dirichletConv hu₁, fun n hn => ?_⟩
  rw [hc₂₃ n hn, dirichletConv_congr (fun _ _ => rfl) hc₁₂ n, ← dirichletConv_assoc]

/-- **`WienerUnitOrbit` is an equivalence relation on arithmetic weights.** -/
theorem equivalence_wienerUnitOrbit : Equivalence WienerUnitOrbit :=
  ⟨wienerUnitOrbit_refl, wienerUnitOrbit_symm, wienerUnitOrbit_trans⟩

theorem wienerMonoidOrbit_refl (c : ℕ → ℝ) : WienerMonoidOrbit c c :=
  ⟨unitKernel, criticalWiener_unitKernel, fun _ hn => (dirichletConv_unitKernel c hn).symm⟩

theorem wienerMonoidOrbit_trans {c₁ c₂ c₃ : ℕ → ℝ}
    (h₁₂ : WienerMonoidOrbit c₁ c₂) (h₂₃ : WienerMonoidOrbit c₂ c₃) :
    WienerMonoidOrbit c₁ c₃ := by
  obtain ⟨k₁, hk₁, hc₁₂⟩ := h₁₂
  obtain ⟨k₂, hk₂, hc₂₃⟩ := h₂₃
  refine ⟨RHTower.dirichletConv k₂ k₁, criticalWiener_dirichletConv hk₂ hk₁, fun n hn => ?_⟩
  rw [hc₂₃ n hn, dirichletConv_congr (fun _ _ => rfl) hc₁₂ n, ← dirichletConv_assoc]

theorem wienerMonoidOrbit_of_wienerUnitOrbit {c₁ c₂ : ℕ → ℝ} (h : WienerUnitOrbit c₁ c₂) :
    WienerMonoidOrbit c₁ c₂ ∧ WienerMonoidOrbit c₂ c₁ := by
  obtain ⟨v, hv, hc'⟩ := wienerUnitOrbit_symm h
  obtain ⟨u, hu, hc⟩ := h
  exact ⟨⟨u, hu.1, hc⟩, ⟨v, hv.1, hc'⟩⟩

/-- `paidIdeal` depends on `c` only at positive integers. -/
theorem paidIdeal_congr_ne_zero {c₁ c₂ : ℕ → ℝ} (h : ∀ n, n ≠ 0 → c₁ n = c₂ n)
    (hc₁ : Summable fun d : ℕ => |c₁ d / d|) (hc₂ : Summable fun d : ℕ => |c₂ d / d|) :
    paidIdeal c₁ hc₁ = paidIdeal c₂ hc₂ := by
  ext k
  rw [mem_paidIdeal, mem_paidIdeal]
  have hconv : ∀ f : ℕ → ℝ, RHTower.dirichletConv f c₁ = RHTower.dirichletConv f c₂ :=
    fun f => funext fun n => dirichletConv_congr (fun _ _ => rfl) h n
  rw [hconv, hconv]

/-- `obstructionHull` depends on `c` only at positive integers. -/
theorem obstructionHull_congr_ne_zero {c₁ c₂ : ℕ → ℝ} (h : ∀ n, n ≠ 0 → c₁ n = c₂ n)
    (hc₁ : Summable fun d : ℕ => |c₁ d / d|) (hc₂ : Summable fun d : ℕ => |c₂ d / d|) :
    obstructionHull c₁ hc₁ = obstructionHull c₂ hc₂ := by
  unfold obstructionHull
  rw [paidIdeal_congr_ne_zero h hc₁ hc₂]

/-- **Payment is constant on `WienerMonoidOrbit` forward cones:** if `c₁` is paid and
`WienerMonoidOrbit c₁ c₂`, then `c₂` is paid. Equivalently, no unpaid weight lies in the monoid
orbit of a paid weight. -/
theorem receiverBounded_of_wienerMonoidOrbit {c₁ c₂ : ℕ → ℝ}
    (hc₁ : Summable fun d : ℕ => |c₁ d / d|) (h : WienerMonoidOrbit c₁ c₂)
    (hpaid : ReceiverBounded c₁) : ReceiverBounded c₂ := by
  obtain ⟨k, hk, hc⟩ := h
  exact (receiverBounded_congr fun n hn => (hc n hn.ne').symm).1
    (receiverBounded_dirichletConv hk hc₁ hpaid)

/-- **Payment is a `WienerUnitOrbit` invariant.** -/
theorem receiverBounded_iff_of_wienerUnitOrbit {c₁ c₂ : ℕ → ℝ}
    (hc₁ : Summable fun d : ℕ => |c₁ d / d|) (hc₂ : Summable fun d : ℕ => |c₂ d / d|)
    (h : WienerUnitOrbit c₁ c₂) :
    ReceiverBounded c₁ ↔ ReceiverBounded c₂ := by
  obtain ⟨h12, h21⟩ := wienerMonoidOrbit_of_wienerUnitOrbit h
  exact ⟨receiverBounded_of_wienerMonoidOrbit hc₁ h12,
    receiverBounded_of_wienerMonoidOrbit hc₂ h21⟩

/-- **The repairing ideal ascends along `WienerMonoidOrbit`:**
`WienerMonoidOrbit c₁ c₂ → paidIdeal c₁ hc₁ ≤ paidIdeal c₂ hc₂`. -/
theorem paidIdeal_le_of_wienerMonoidOrbit {c₁ c₂ : ℕ → ℝ}
    (hc₁ : Summable fun d : ℕ => |c₁ d / d|) (hc₂ : Summable fun d : ℕ => |c₂ d / d|)
    (h : WienerMonoidOrbit c₁ c₂) :
    paidIdeal c₁ hc₁ ≤ paidIdeal c₂ hc₂ := by
  obtain ⟨k₀, hk₀, hc⟩ := h
  rw [paidIdeal_congr_ne_zero hc hc₂ (summable_abs_dirichletConv_div hk₀ hc₁)]
  intro k hk
  exact (mem_paidIdeal_conv_iff c₁ hc₁ hk₀ k).2 (Ideal.mul_mem_right _ _ hk)

/-- **The obstruction hull descends along `WienerMonoidOrbit`:**
`WienerMonoidOrbit c₁ c₂ → obstructionHull c₂ hc₂ ⊆ obstructionHull c₁ hc₁`. -/
theorem obstructionHull_subset_of_wienerMonoidOrbit {c₁ c₂ : ℕ → ℝ}
    (hc₁ : Summable fun d : ℕ => |c₁ d / d|) (hc₂ : Summable fun d : ℕ => |c₂ d / d|)
    (h : WienerMonoidOrbit c₁ c₂) :
    obstructionHull c₂ hc₂ ⊆ obstructionHull c₁ hc₁ :=
  fun _ hω k hk => hω k (paidIdeal_le_of_wienerMonoidOrbit hc₁ hc₂ h hk)

/-- **The quotient rank (obstruction codimension) descends along `WienerMonoidOrbit`:**
`WienerMonoidOrbit c₁ c₂ → Module.rank ℂ (𝒲_{1/2} ⧸ paidIdeal c₂ hc₂) ≤ Module.rank ℂ (𝒲_{1/2} ⧸ paidIdeal c₁ hc₁)`. -/
theorem rank_quotient_paidIdeal_le_of_wienerMonoidOrbit {c₁ c₂ : ℕ → ℝ}
    (hc₁ : Summable fun d : ℕ => |c₁ d / d|) (hc₂ : Summable fun d : ℕ => |c₂ d / d|)
    (h : WienerMonoidOrbit c₁ c₂) :
    Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸ paidIdeal c₂ hc₂) ≤
      Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸ paidIdeal c₁ hc₁) := by
  have hle := paidIdeal_le_of_wienerMonoidOrbit hc₁ hc₂ h
  let L := Ideal.Quotient.liftₐ (paidIdeal c₁ hc₁)
    (Ideal.Quotient.mkₐ ℂ (paidIdeal c₂ hc₂))
    (fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (hle hx))
  have hsurj : Function.Surjective L := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk (paidIdeal c₁ hc₁) x, rfl⟩
  have hrank := rank_range_le L.toLinearMap
  rwa [LinearMap.range_eq_top.2 hsurj, rank_top] at hrank

/-- **The repairing ideal, obstruction hull, and quotient codimension are `WienerUnitOrbit`
invariants.** -/
theorem paidIdeal_eq_of_wienerUnitOrbit {c₁ c₂ : ℕ → ℝ}
    (hc₁ : Summable fun d : ℕ => |c₁ d / d|) (hc₂ : Summable fun d : ℕ => |c₂ d / d|)
    (h : WienerUnitOrbit c₁ c₂) :
    paidIdeal c₁ hc₁ = paidIdeal c₂ hc₂ := by
  obtain ⟨h12, h21⟩ := wienerMonoidOrbit_of_wienerUnitOrbit h
  exact le_antisymm (paidIdeal_le_of_wienerMonoidOrbit hc₁ hc₂ h12)
    (paidIdeal_le_of_wienerMonoidOrbit hc₂ hc₁ h21)

theorem obstructionHull_eq_of_wienerUnitOrbit {c₁ c₂ : ℕ → ℝ}
    (hc₁ : Summable fun d : ℕ => |c₁ d / d|) (hc₂ : Summable fun d : ℕ => |c₂ d / d|)
    (h : WienerUnitOrbit c₁ c₂) :
    obstructionHull c₁ hc₁ = obstructionHull c₂ hc₂ := by
  unfold obstructionHull
  rw [paidIdeal_eq_of_wienerUnitOrbit hc₁ hc₂ h]

theorem rank_quotient_paidIdeal_eq_of_wienerUnitOrbit {c₁ c₂ : ℕ → ℝ}
    (hc₁ : Summable fun d : ℕ => |c₁ d / d|) (hc₂ : Summable fun d : ℕ => |c₂ d / d|)
    (h : WienerUnitOrbit c₁ c₂) :
    Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸ paidIdeal c₁ hc₁) =
      Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸ paidIdeal c₂ hc₂) ∧
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸ paidIdeal c₁ hc₁) =
      Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸ paidIdeal c₂ hc₂) := by
  rw [paidIdeal_eq_of_wienerUnitOrbit hc₁ hc₂ h]
  exact ⟨rfl, rfl⟩

/-! ### 2. Sharp stabilizer–annihilator dichotomy on principal and conjugate-pair orbits -/

/-- **Stabilizer–annihilator dichotomy for any weight with a single-point Bohr character ideal:**
if `paidIdeal c hc = RingHom.ker (bohrCharacter (1 / 2) ω₀)` and `CriticalWiener k₀`, then:
- if `bohrEval (1 / 2) (realFn k₀) ω₀ = 0`, `k₀ ⋆ c` is paid (`paidIdeal = ⊤`,
  `obstructionHull = ∅`, `finrank = 0`);
- if `bohrEval (1 / 2) (realFn k₀) ω₀ ≠ 0`, `k₀ ⋆ c` is unpaid with the **exact same**
  `paidIdeal (k₀ ⋆ c) = paidIdeal c hc`, the **exact same** `obstructionHull (k₀ ⋆ c) = obstructionHull c hc`,
  and `Module.finrank ℂ (𝒲_{1/2} ⧸ paidIdeal (k₀ ⋆ c)) = 1`. -/
theorem paidIdeal_conv_dichotomy_of_eq_ker {c : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|)
    {ω₀ : BohrPoint} (hker : paidIdeal c hc = RingHom.ker (WienerAlgebraAt.bohrCharacter (1 / 2) ω₀))
    {k₀ : ℕ → ℝ} (hk₀ : CriticalWiener k₀) :
    (bohrEval (1 / 2) (realFn k₀) ω₀ = 0 →
      ReceiverBounded (RHTower.dirichletConv k₀ c) ∧
      paidIdeal (RHTower.dirichletConv k₀ c) (summable_abs_dirichletConv_div hk₀ hc) = ⊤ ∧
      obstructionHull (RHTower.dirichletConv k₀ c) (summable_abs_dirichletConv_div hk₀ hc) = ∅ ∧
      Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (RHTower.dirichletConv k₀ c) (summable_abs_dirichletConv_div hk₀ hc)) = 0) ∧
    (bohrEval (1 / 2) (realFn k₀) ω₀ ≠ 0 →
      ¬ ReceiverBounded (RHTower.dirichletConv k₀ c) ∧
      paidIdeal (RHTower.dirichletConv k₀ c) (summable_abs_dirichletConv_div hk₀ hc) =
        paidIdeal c hc ∧
      obstructionHull (RHTower.dirichletConv k₀ c) (summable_abs_dirichletConv_div hk₀ hc) =
        obstructionHull c hc ∧
      Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (RHTower.dirichletConv k₀ c) (summable_abs_dirichletConv_div hk₀ hc)) = 1) := by
  have hmem : ∀ k : WienerAlgebraAt (1 / 2),
      k ∈ paidIdeal (RHTower.dirichletConv k₀ c) (summable_abs_dirichletConv_div hk₀ hc) ↔
        bohrEval (1 / 2) k.toFn ω₀ * bohrEval (1 / 2) (realFn k₀) ω₀ = 0 := fun k => by
    rw [mem_paidIdeal_conv_iff c hc hk₀ k, hker, RingHom.mem_ker, _root_.map_mul,
      bohrCharacter_apply, bohrCharacter_apply]
    rfl
  constructor
  · intro hz
    have htop : paidIdeal (RHTower.dirichletConv k₀ c) (summable_abs_dirichletConv_div hk₀ hc) = ⊤ := by
      ext k
      rw [hmem k, hz, mul_zero]
      simp
    have hpaid : ReceiverBounded (RHTower.dirichletConv k₀ c) :=
      (one_mem_paidIdeal_iff _ _).1 (htop ▸ Submodule.mem_top)
    have hhull : obstructionHull (RHTower.dirichletConv k₀ c)
        (summable_abs_dirichletConv_div hk₀ hc) = ∅ :=
      Set.not_nonempty_iff_eq_empty.1 (by rw [obstructionHull_nonempty_iff]; exact not_not.2 hpaid)
    have hfin : Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (RHTower.dirichletConv k₀ c) (summable_abs_dirichletConv_div hk₀ hc)) = 0 := by
      rw [htop]
      haveI : Subsingleton (WienerAlgebraAt (1 / 2) ⧸ (⊤ : Ideal (WienerAlgebraAt (1 / 2)))) :=
        Ideal.Quotient.subsingleton_iff.2 rfl
      exact Module.finrank_zero_of_subsingleton
    exact ⟨hpaid, htop, hhull, hfin⟩
  · intro hnz
    have hid : paidIdeal (RHTower.dirichletConv k₀ c) (summable_abs_dirichletConv_div hk₀ hc) =
        paidIdeal c hc := by
      ext k
      rw [hmem k, mul_eq_zero, or_iff_left hnz, hker, RingHom.mem_ker, bohrCharacter_apply]
    have hhull : obstructionHull (RHTower.dirichletConv k₀ c)
        (summable_abs_dirichletConv_div hk₀ hc) = obstructionHull c hc := by
      unfold obstructionHull; rw [hid]
    have hfin : Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (RHTower.dirichletConv k₀ c) (summable_abs_dirichletConv_div hk₀ hc)) = 1 := by
      rw [hid, hker]
      exact finrank_quotient_ker_bohrCharacter ω₀
    have hunpaid : ¬ ReceiverBounded (RHTower.dirichletConv k₀ c) := by
      rw [← one_mem_paidIdeal_iff _ (summable_abs_dirichletConv_div hk₀ hc),
        hid, hker, RingHom.mem_ker, _root_.map_one]
      exact one_ne_zero
    exact ⟨hunpaid, hid, hhull, hfin⟩

/-- **Real-kernel conjugate-pair dichotomy on the oscillating probe:**
for `0 < ε < 1/2`, `t ≠ 0`, `ζ(ρ) ≠ 0` (`ρ = 1 − ε + it`), and any **real** critical Wiener kernel
`k₀`, `bohrEval` at `ρ̄` is the conjugate of `bohrEval` at `ρ`, so:
- if `complexPoleValue k₀ ρ = 0`, `k₀ ⋆ oscillatingSmoothPower ε t` is paid with `paidIdeal = ⊤`,
  `obstructionHull = ∅`, and `finrank = 0`;
- if `complexPoleValue k₀ ρ ≠ 0`, `k₀ ⋆ oscillatingSmoothPower ε t` is unpaid with the **exact same**
  two-point repairing ideal `paidIdeal`, the **exact same** `obstructionHull = {ρ, ρ̄}`, and
  `finrank = 2` (in particular, no real convolution ever has codimension `1`). -/
theorem paidIdeal_oscillating_conv_dichotomy {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {t : ℝ}
    (ht : t ≠ 0) (hz : riemannZeta (oscillationExponent ε t) ≠ 0) {k₀ : ℕ → ℝ}
    (hk₀ : CriticalWiener k₀) :
    (complexPoleValue k₀ (oscillationExponent ε t) = 0 →
      ReceiverBounded (RHTower.dirichletConv k₀ (oscillatingSmoothPower ε t)) ∧
      paidIdeal (RHTower.dirichletConv k₀ (oscillatingSmoothPower ε t))
        (summable_abs_dirichletConv_div hk₀ (summable_abs_oscillatingSmoothPower_div hε t)) = ⊤ ∧
      Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (RHTower.dirichletConv k₀ (oscillatingSmoothPower ε t))
          (summable_abs_dirichletConv_div hk₀ (summable_abs_oscillatingSmoothPower_div hε t))) = 0) ∧
    (complexPoleValue k₀ (oscillationExponent ε t) ≠ 0 →
      ¬ ReceiverBounded (RHTower.dirichletConv k₀ (oscillatingSmoothPower ε t)) ∧
      paidIdeal (RHTower.dirichletConv k₀ (oscillatingSmoothPower ε t))
        (summable_abs_dirichletConv_div hk₀ (summable_abs_oscillatingSmoothPower_div hε t)) =
        paidIdeal (oscillatingSmoothPower ε t) (summable_abs_oscillatingSmoothPower_div hε t) ∧
      obstructionHull (RHTower.dirichletConv k₀ (oscillatingSmoothPower ε t))
        (summable_abs_dirichletConv_div hk₀ (summable_abs_oscillatingSmoothPower_div hε t)) =
        obstructionHull (oscillatingSmoothPower ε t) (summable_abs_oscillatingSmoothPower_div hε t) ∧
      Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (RHTower.dirichletConv k₀ (oscillatingSmoothPower ε t))
          (summable_abs_dirichletConv_div hk₀ (summable_abs_oscillatingSmoothPower_div hε t))) = 2) := by
  set ρ := oscillationExponent ε t
  set hc := summable_abs_oscillatingSmoothPower_div hε t
  have hre : rePart (toWiener k₀ hk₀) = fun n => if n = 0 then 0 else k₀ n := funext fun n => by
    rcases eq_or_ne n 0 with rfl | hn <;> simp [rePart, toWiener, toFn_mk, realFn, *]
  have him : imPart (toWiener k₀ hk₀) = fun _ => 0 := funext fun n => by
    rcases eq_or_ne n 0 with rfl | hn <;> simp [imPart, toWiener, toFn_mk, realFn, *]
  have hpole_re : ∀ z : ℂ, 1 / 2 ≤ z.re →
      complexPoleValue (rePart (toWiener k₀ hk₀)) z = complexPoleValue k₀ z := fun z hzre => by
    unfold complexPoleValue
    refine tsum_congr fun j => ?_
    rcases eq_or_ne j 0 with rfl | hj
    · have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hzre; linarith
      simp [Complex.zero_cpow (neg_ne_zero.2 hz0)]
    · rw [hre]; dsimp only; rw [if_neg hj]
  have hpole_im : ∀ z : ℂ, complexPoleValue (imPart (toWiener k₀ hk₀)) z = 0 := fun z => by
    unfold complexPoleValue; simp [him]
  have hev₁ : bohrEval (1 / 2) (toWiener k₀ hk₀).toFn (oscPoint ε t hε2) =
      complexPoleValue k₀ ρ := by
    rw [oscPoint, bohrEval_halfPlanePoint,
      lSeries_eq_complexPoleValue _ (half_le_re_oscillationExponent hε2 t),
      hpole_re _ (half_le_re_oscillationExponent hε2 t), hpole_im, mul_zero, add_zero]
  have hev₂ : bohrEval (1 / 2) (toWiener k₀ hk₀).toFn (oscPointConj ε t hε2) =
      starRingEnd ℂ (complexPoleValue k₀ ρ) := by
    rw [oscPointConj, bohrEval_halfPlanePoint,
      lSeries_eq_complexPoleValue _ (half_le_re_conj_oscillationExponent hε2 t),
      hpole_re _ (half_le_re_conj_oscillationExponent hε2 t), hpole_im, mul_zero, add_zero,
      complexPoleValue_conj]
  have hmul_eval : ∀ (k : WienerAlgebraAt (1 / 2)) (ν : BohrPoint),
      bohrEval (1 / 2) (k * toWiener k₀ hk₀).toFn ν =
        bohrEval (1 / 2) k.toFn ν * bohrEval (1 / 2) (toWiener k₀ hk₀).toFn ν := fun k ν => by
    rw [← bohrCharacter_apply, _root_.map_mul, bohrCharacter_apply, bohrCharacter_apply]
  have hmem : ∀ k : WienerAlgebraAt (1 / 2),
      k ∈ paidIdeal (RHTower.dirichletConv k₀ (oscillatingSmoothPower ε t))
          (summable_abs_dirichletConv_div hk₀ hc) ↔
        bohrEval (1 / 2) k.toFn (oscPoint ε t hε2) * complexPoleValue k₀ ρ = 0 ∧
        bohrEval (1 / 2) k.toFn (oscPointConj ε t hε2) *
          starRingEnd ℂ (complexPoleValue k₀ ρ) = 0 := fun k => by
    rw [mem_paidIdeal_conv_iff _ hc hk₀ k, mem_paidIdeal_oscillating_iff hε hε2 hz,
      hmul_eval, hmul_eval, hev₁, hev₂]
  constructor
  · intro h0
    have htop : paidIdeal (RHTower.dirichletConv k₀ (oscillatingSmoothPower ε t))
        (summable_abs_dirichletConv_div hk₀ hc) = ⊤ := by
      ext k; simp [hmem k, h0]
    have hpaid : ReceiverBounded (RHTower.dirichletConv k₀ (oscillatingSmoothPower ε t)) :=
      (one_mem_paidIdeal_iff _ _).1 (htop ▸ Submodule.mem_top)
    have hfin : Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (RHTower.dirichletConv k₀ (oscillatingSmoothPower ε t))
          (summable_abs_dirichletConv_div hk₀ hc)) = 0 := by
      rw [htop]
      haveI : Subsingleton (WienerAlgebraAt (1 / 2) ⧸ (⊤ : Ideal (WienerAlgebraAt (1 / 2)))) :=
        Ideal.Quotient.subsingleton_iff.2 rfl
      exact Module.finrank_zero_of_subsingleton
    exact ⟨hpaid, htop, hfin⟩
  · intro hnz
    have hnz_conj : starRingEnd ℂ (complexPoleValue k₀ ρ) ≠ 0 :=
      map_ne_zero_iff (starRingEnd ℂ) (RingHom.injective _) |>.2 hnz
    have hid : paidIdeal (RHTower.dirichletConv k₀ (oscillatingSmoothPower ε t))
        (summable_abs_dirichletConv_div hk₀ hc) = paidIdeal (oscillatingSmoothPower ε t) hc := by
      ext k
      rw [hmem k, mul_eq_zero, mul_eq_zero, or_iff_left hnz, or_iff_left hnz_conj,
        mem_paidIdeal_oscillating_iff hε hε2 hz]
    have hhull : obstructionHull (RHTower.dirichletConv k₀ (oscillatingSmoothPower ε t))
        (summable_abs_dirichletConv_div hk₀ hc) =
        obstructionHull (oscillatingSmoothPower ε t) hc := by
      unfold obstructionHull; rw [hid]
    have hfin : Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (RHTower.dirichletConv k₀ (oscillatingSmoothPower ε t))
          (summable_abs_dirichletConv_div hk₀ hc)) = 2 := by
      rw [hid]
      exact finrank_quotient_paidIdeal_oscillating hε hε2 ht hz
    have hunpaid : ¬ ReceiverBounded (RHTower.dirichletConv k₀ (oscillatingSmoothPower ε t)) := by
      rw [← obstructionHull_nonempty_iff _ (summable_abs_dirichletConv_div hk₀ hc), hhull]
      exact (obstructionHull_oscillating_nonempty_iff hε hε2 t).2 hz
    exact ⟨hunpaid, hid, hhull, hfin⟩

/-! ### 3. Dirichlet cancellation and infinite irreversible chains inside a single obstruction hull -/

/-- **Dirichlet cancellation for any weight normalized at `1` (`c 1 ≠ 0`):**
if `c 1 ≠ 0`, then Dirichlet convolution with `c` is injective away from `0`:
`(∀ n ≠ 0, (k₁ ⋆ c) n = (k₂ ⋆ c) n) ↔ (∀ n ≠ 0, k₁ n = k₂ n)`. -/
theorem dirichletConv_right_inj_of_apply_one_ne_zero {c : ℕ → ℝ} (hc1 : c 1 ≠ 0)
    (k₁ k₂ : ℕ → ℝ) :
    (∀ n : ℕ, n ≠ 0 → RHTower.dirichletConv k₁ c n = RHTower.dirichletConv k₂ c n) ↔
      (∀ n : ℕ, n ≠ 0 → k₁ n = k₂ n) := by
  refine ⟨fun h n => ?_, fun h n _ => dirichletConv_congr h (fun _ _ => rfl) n⟩
  induction' n using Nat.strong_induction_on with n ih
  intro hn
  have hmem : n ∈ n.divisors := Nat.mem_divisors.2 ⟨dvd_rfl, hn⟩
  have hsplit : ∀ k : ℕ → ℝ, RHTower.dirichletConv k c n =
      (∑ d ∈ n.divisors.erase n, k d * c (n / d)) + k n * c 1 := fun k => by
    unfold RHTower.dirichletConv
    rw [← Finset.sum_erase_add _ _ hmem, Nat.div_self (Nat.pos_of_ne_zero hn)]
  have hsum : ∑ d ∈ n.divisors.erase n, k₁ d * c (n / d) =
      ∑ d ∈ n.divisors.erase n, k₂ d * c (n / d) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    have hne : d ≠ n := (Finset.mem_erase.1 hd).1
    have hdvd : d ∈ n.divisors := (Finset.mem_erase.1 hd).2
    have hle : d ≤ n := Nat.divisor_le hdvd
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hdvd).ne'
    rw [ih d (lt_of_le_of_ne hle hne) hd0]
  have hn_eq := h n hn
  rw [hsplit k₁, hsplit k₂, hsum, add_right_inj] at hn_eq
  exact mul_right_cancel₀ hc1 hn_eq

/-- **Exact monoid-recovery criterion for normalized weights (`c 1 ≠ 0`):**
for any weight `c` with `c 1 ≠ 0` and any critical Wiener kernel `k` (`CriticalWiener k`),
`c` lies in the monoid orbit of `k ⋆ c` if and only if `k` is a unit of the critical Wiener monoid
(`IsWienerUnit k`). -/
theorem wienerMonoidOrbit_conv_self_iff {c : ℕ → ℝ} (hc1 : c 1 ≠ 0) {k : ℕ → ℝ}
    (hk : CriticalWiener k) :
    WienerMonoidOrbit (RHTower.dirichletConv k c) c ↔ IsWienerUnit k := by
  constructor
  · rintro ⟨g, hg, hrec⟩
    refine ⟨hk, g, hg, fun n hn => ?_⟩
    rw [dirichletConv_comm]
    have hconv : ∀ m : ℕ, m ≠ 0 →
        RHTower.dirichletConv (RHTower.dirichletConv g k) c m =
          RHTower.dirichletConv unitKernel c m := fun m hm => by
      rw [dirichletConv_assoc, ← hrec m hm, dirichletConv_unitKernel c hm]
    exact (dirichletConv_right_inj_of_apply_one_ne_zero hc1 _ _).1 hconv n hn
  · intro hu
    exact (wienerMonoidOrbit_of_wienerUnitOrbit ⟨k, hu, fun _ _ => rfl⟩).2

/-- **Exact unit-orbit criterion for normalized weights (`c 1 ≠ 0`):**
for any weight `c` with `c 1 ≠ 0` and any critical Wiener kernel `k` (`CriticalWiener k`),
`k ⋆ c` lies in the unit orbit of `c` if and only if `IsWienerUnit k`. -/
theorem wienerUnitOrbit_conv_self_iff {c : ℕ → ℝ} (hc1 : c 1 ≠ 0) {k : ℕ → ℝ}
    (hk : CriticalWiener k) :
    WienerUnitOrbit c (RHTower.dirichletConv k c) ↔ IsWienerUnit k := by
  constructor
  · intro hu
    exact (wienerMonoidOrbit_conv_self_iff hc1 hk).1
      (wienerMonoidOrbit_of_wienerUnitOrbit hu).2
  · intro hu
    exact ⟨k, hu, fun _ _ => rfl⟩

/-- The real three-term kernel `δ₁ − ½√2 δ₂ + ½√3 δ₃` as a real function `ℕ → ℝ`. -/
def realThreeTermKernel : ℕ → ℝ := rePart threeTermKernel

theorem criticalWiener_realThreeTermKernel : CriticalWiener realThreeTermKernel :=
  criticalWiener_rePart threeTermKernel

theorem imPart_threeTermKernel : imPart threeTermKernel = fun _ => 0 := by
  funext n
  have h2 : ((2 : ℂ) ^ (2⁻¹ : ℂ)).im = 0 := by
    have h : (2 : ℂ) ^ (2⁻¹ : ℂ) = (((2 : ℝ) ^ (2⁻¹ : ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by norm_num)]; norm_num
    rw [h, Complex.ofReal_im]
  have h3 : ((3 : ℂ) ^ (2⁻¹ : ℂ)).im = 0 := by
    have h : (3 : ℂ) ^ (2⁻¹ : ℂ) = (((3 : ℝ) ^ (2⁻¹ : ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by norm_num)]; norm_num
    rw [h, Complex.ofReal_im]
  simp only [imPart, threeTermKernel, sub_eq_add_neg, toFn_add, toFn_neg, toFn_one, toFn_smul,
    toFn_pointMass, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply,
    smul_map, one_apply, pointMassFn_apply, smul_eq_mul]
  split_ifs <;> simp [h2, h3]

theorem toWiener_realThreeTermKernel :
    toWiener realThreeTermKernel criticalWiener_realThreeTermKernel = threeTermKernel := by
  apply WienerAlgebraAt.ext
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have him : (threeTermKernel.toFn n).im = 0 := congrFun imPart_threeTermKernel n
    rw [toWiener, toFn_mk, realFn_apply hn, Complex.ext_iff]
    exact ⟨rfl, him.symm⟩

theorem realThreeTermKernel_one : realThreeTermKernel 1 = 1 := by
  simp [realThreeTermKernel, rePart, threeTermKernel, sub_eq_add_neg, toFn_add, toFn_neg,
    toFn_one, toFn_smul, toFn_pointMass, smul_map, one_apply, pointMassFn_apply]

/-- **`realThreeTermKernel` is not a unit of the critical Wiener monoid.** -/
theorem not_isWienerUnit_realThreeTermKernel : ¬ IsWienerUnit realThreeTermKernel := by
  rw [isWienerUnit_iff_isUnit _ criticalWiener_realThreeTermKernel, toWiener_realThreeTermKernel]
  exact not_isUnit_threeTermKernel

/-- **`realThreeTermKernel` has nonvanishing Bohr evaluation at every half-plane point `Re s ≥ ½`.** -/
theorem bohrEval_realThreeTermKernel_halfPlanePoint_ne_zero {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    bohrEval (1 / 2) (realFn realThreeTermKernel) (halfPlanePoint (1 / 2) s hs) ≠ 0 := by
  have hfn : realFn realThreeTermKernel = threeTermKernel.toFn := by
    rw [← toWiener_realThreeTermKernel]; rfl
  rw [hfn, bohrEval_halfPlanePoint]
  exact lSeries_threeTermKernel_ne_zero hs

/-- Iterated convolution `(realThreeTermKernel ⋆ ·)^[m] c` by the three-term kernel. -/
def iterThreeTermConv : ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | 0, c => c
  | m + 1, c => RHTower.dirichletConv realThreeTermKernel (iterThreeTermConv m c)

@[simp]
theorem iterThreeTermConv_zero (c : ℕ → ℝ) : iterThreeTermConv 0 c = c := rfl

@[simp]
theorem iterThreeTermConv_succ (m : ℕ) (c : ℕ → ℝ) :
    iterThreeTermConv (m + 1) c = RHTower.dirichletConv realThreeTermKernel (iterThreeTermConv m c) :=
  rfl

theorem iterThreeTermConv_apply_one (m : ℕ) (c : ℕ → ℝ) :
    iterThreeTermConv m c 1 = c 1 := by
  induction' m with m ih
  · rfl
  · rw [iterThreeTermConv_succ, RHTower.dirichletConv, Nat.divisors_one, sum_singleton,
      Nat.div_one, realThreeTermKernel_one, one_mul, ih]

theorem summable_abs_iterThreeTermConv_div : ∀ (m : ℕ) {c : ℕ → ℝ},
    Summable (fun d : ℕ => |c d / d|) →
    Summable (fun d : ℕ => |iterThreeTermConv m c d / d|)
  | 0, _, hc => hc
  | m + 1, _, hc =>
      summable_abs_dirichletConv_div criticalWiener_realThreeTermKernel
        (summable_abs_iterThreeTermConv_div m hc)

/-- **One step along `iterThreeTermConv` is strictly irreversible in `WienerMonoidOrbit` for every
normalized weight (`c 1 ≠ 0`):**
`WienerMonoidOrbit (iterThreeTermConv m c) (iterThreeTermConv (m + 1) c)` holds, while
`¬ WienerMonoidOrbit (iterThreeTermConv (m + 1) c) (iterThreeTermConv m c)` and
`¬ WienerUnitOrbit (iterThreeTermConv m c) (iterThreeTermConv (m + 1) c)`. -/
theorem iterThreeTermConv_step_strict (m : ℕ) {c : ℕ → ℝ} (hc1 : c 1 ≠ 0) :
    WienerMonoidOrbit (iterThreeTermConv m c) (iterThreeTermConv (m + 1) c) ∧
    ¬ WienerMonoidOrbit (iterThreeTermConv (m + 1) c) (iterThreeTermConv m c) ∧
    ¬ WienerUnitOrbit (iterThreeTermConv m c) (iterThreeTermConv (m + 1) c) := by
  have hm1 : iterThreeTermConv m c 1 ≠ 0 := by rw [iterThreeTermConv_apply_one]; exact hc1
  rw [iterThreeTermConv_succ]
  refine ⟨⟨realThreeTermKernel, criticalWiener_realThreeTermKernel, fun _ _ => rfl⟩, ?_, ?_⟩
  · rw [wienerMonoidOrbit_conv_self_iff hm1 criticalWiener_realThreeTermKernel]
    exact not_isWienerUnit_realThreeTermKernel
  · rw [wienerUnitOrbit_conv_self_iff hm1 criticalWiener_realThreeTermKernel]
    exact not_isWienerUnit_realThreeTermKernel

/-- **Infinite strictly descending `WienerMonoidOrbit` chain inside the single-point obstruction
hull of the smooth power `d^{−ε}`:**
for `0 < ε < 1/2` and every `m : ℕ`, `iterThreeTermConv m (dampedSignWeight unitSign ε)` is unpaid
with the **exact same** repairing ideal `paidIdeal (d^{−ε})`, the **exact same** obstruction hull
`obstructionHull (d^{−ε}) = {polePoint ε}`, and codimension `1`, while every step `m → m + 1` is a
strictly irreversible monoid transition outside the unit orbit. -/
theorem iterThreeTermConv_smoothPower_chain {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (m : ℕ) :
    ¬ ReceiverBounded (iterThreeTermConv m (dampedSignWeight unitSign ε)) ∧
    paidIdeal (iterThreeTermConv m (dampedSignWeight unitSign ε))
      (summable_abs_iterThreeTermConv_div m (summable_abs_smoothPower_div hε)) =
      paidIdeal (dampedSignWeight unitSign ε) (summable_abs_smoothPower_div hε) ∧
    obstructionHull (iterThreeTermConv m (dampedSignWeight unitSign ε))
      (summable_abs_iterThreeTermConv_div m (summable_abs_smoothPower_div hε)) =
      obstructionHull (dampedSignWeight unitSign ε) (summable_abs_smoothPower_div hε) ∧
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
      paidIdeal (iterThreeTermConv m (dampedSignWeight unitSign ε))
        (summable_abs_iterThreeTermConv_div m (summable_abs_smoothPower_div hε))) = 1 ∧
    WienerMonoidOrbit (iterThreeTermConv m (dampedSignWeight unitSign ε))
      (iterThreeTermConv (m + 1) (dampedSignWeight unitSign ε)) ∧
    ¬ WienerMonoidOrbit (iterThreeTermConv (m + 1) (dampedSignWeight unitSign ε))
      (iterThreeTermConv m (dampedSignWeight unitSign ε)) ∧
    ¬ WienerUnitOrbit (iterThreeTermConv m (dampedSignWeight unitSign ε))
      (iterThreeTermConv (m + 1) (dampedSignWeight unitSign ε)) := by
  have hu1 : dampedSignWeight unitSign ε 1 ≠ 0 := by simp [dampedSignWeight, unitSign]
  have hpres : ¬ ReceiverBounded (iterThreeTermConv m (dampedSignWeight unitSign ε)) ∧
      paidIdeal (iterThreeTermConv m (dampedSignWeight unitSign ε))
        (summable_abs_iterThreeTermConv_div m (summable_abs_smoothPower_div hε)) =
        paidIdeal (dampedSignWeight unitSign ε) (summable_abs_smoothPower_div hε) ∧
      obstructionHull (iterThreeTermConv m (dampedSignWeight unitSign ε))
        (summable_abs_iterThreeTermConv_div m (summable_abs_smoothPower_div hε)) =
        obstructionHull (dampedSignWeight unitSign ε) (summable_abs_smoothPower_div hε) ∧
      Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (iterThreeTermConv m (dampedSignWeight unitSign ε))
          (summable_abs_iterThreeTermConv_div m (summable_abs_smoothPower_div hε))) = 1 := by
    induction' m with m ih
    · refine ⟨?_, rfl, rfl, finrank_quotient_paidIdeal_smoothPower hε hε2⟩
      rw [iterThreeTermConv_zero, ← obstructionHull_nonempty_iff _ (summable_abs_smoothPower_div hε)]
      exact ⟨polePoint ε hε2.le, (mem_obstructionHull_smoothPower_iff hε hε2 _).2 fun _ _ => rfl⟩
    · obtain ⟨_, hid, hhull, _⟩ := ih
      have hker : paidIdeal (iterThreeTermConv m (dampedSignWeight unitSign ε))
          (summable_abs_iterThreeTermConv_div m (summable_abs_smoothPower_div hε)) =
          RingHom.ker (WienerAlgebraAt.bohrCharacter (1 / 2) (polePoint ε hε2.le)) :=
        hid.trans (paidIdeal_smoothPower_eq_ker hε hε2)
      have hnz : bohrEval (1 / 2) (realFn realThreeTermKernel) (polePoint ε hε2.le) ≠ 0 :=
        bohrEval_realThreeTermKernel_halfPlanePoint_ne_zero (by simp; linarith)
      have hdic := (paidIdeal_conv_dichotomy_of_eq_ker
        (summable_abs_iterThreeTermConv_div m (summable_abs_smoothPower_div hε))
        hker criticalWiener_realThreeTermKernel).2 hnz
      exact ⟨hdic.1, hdic.2.1.trans hid, hdic.2.2.1.trans hhull, hdic.2.2.2⟩
  have hstep := iterThreeTermConv_step_strict m hu1
  exact ⟨hpres.1, hpres.2.1, hpres.2.2.1, hpres.2.2.2, hstep.1, hstep.2.1, hstep.2.2⟩

/-! ### 4. One-way orientation transitions and incomparable unpaid cones -/

/-- **On the damped Möbius receiver `μ(d) d^{−ε}`, the even flip is an irreversible monoid
transition outside the unit orbit (`0 < ε ≤ 1/2`):**
- `pmPowerDampedRealWeight ε` and its odd part `moebiusOddPart ε` lie in the same `WienerUnitOrbit`;
- `evenFlip (pmPowerDampedRealWeight ε)` lies in the `WienerMonoidOrbit` of
  `pmPowerDampedRealWeight ε`;
- yet `pmPowerDampedRealWeight ε` does **not** lie in the `WienerMonoidOrbit` of
  `evenFlip (pmPowerDampedRealWeight ε)`, and they do **not** lie in the same `WienerUnitOrbit`. -/
theorem moebius_evenFlip_oneWay_orbit {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    WienerUnitOrbit (moebiusOddPart ε) (pmPowerDampedRealWeight ε) ∧
    WienerMonoidOrbit (pmPowerDampedRealWeight ε) (evenFlip (pmPowerDampedRealWeight ε)) ∧
    ¬ WienerMonoidOrbit (evenFlip (pmPowerDampedRealWeight ε)) (pmPowerDampedRealWeight ε) ∧
    ¬ WienerUnitOrbit (pmPowerDampedRealWeight ε) (evenFlip (pmPowerDampedRealWeight ε)) := by
  have hu : IsWienerUnit (twoPoint 1 (-(2 : ℝ) ^ (-ε))) :=
    (isWienerUnit_twoPoint_one_iff _).2 (abs_two_rpow_neg_lt_sqrt_two hε)
  have hu_orb : WienerUnitOrbit (moebiusOddPart ε) (pmPowerDampedRealWeight ε) :=
    ⟨twoPoint 1 (-(2 : ℝ) ^ (-ε)), hu,
      fun n _ => congrFun (pmPowerDampedRealWeight_eq_dirichletConv ε) n⟩
  have hmon_flip : WienerMonoidOrbit (moebiusOddPart ε) (evenFlip (pmPowerDampedRealWeight ε)) :=
    ⟨twoPoint (1 - (2 : ℝ) ^ (-ε)) ((2 : ℝ) ^ (-ε)), criticalWiener_twoPoint _ _,
      fun n _ => congrFun (evenFlip_moebius ε) n⟩
  have h12 : WienerMonoidOrbit (pmPowerDampedRealWeight ε) (evenFlip (pmPowerDampedRealWeight ε)) :=
    wienerMonoidOrbit_trans (wienerMonoidOrbit_of_wienerUnitOrbit hu_orb).2 hmon_flip
  have hodd1 : moebiusOddPart ε 1 ≠ 0 := by
    simp [moebiusOddPart, pmPowerDampedRealWeight, moebiusReal]
  have hnot_mon : ¬ WienerMonoidOrbit (evenFlip (pmPowerDampedRealWeight ε))
      (pmPowerDampedRealWeight ε) := by
    intro hback
    have hback_odd : WienerMonoidOrbit
        (RHTower.dirichletConv (twoPoint (1 - (2 : ℝ) ^ (-ε)) ((2 : ℝ) ^ (-ε))) (moebiusOddPart ε))
        (moebiusOddPart ε) := by
      rw [← evenFlip_moebius ε]
      exact wienerMonoidOrbit_trans hback (wienerMonoidOrbit_of_wienerUnitOrbit hu_orb).2
    have hunit := (wienerMonoidOrbit_conv_self_iff hodd1 (criticalWiener_twoPoint _ _)).1 hback_odd
    exact not_isWienerUnit_flipKernel_moebius hε hε2 hunit
  have hnot_unit : ¬ WienerUnitOrbit (pmPowerDampedRealWeight ε)
      (evenFlip (pmPowerDampedRealWeight ε)) :=
    fun hun => hnot_mon (wienerMonoidOrbit_of_wienerUnitOrbit hun).2
  exact ⟨hu_orb, h12, hnot_mon, hnot_unit⟩

/-- Distinct damping exponents `0 < ε₁ < 1/2` and `0 < ε₂ < 1/2` (`ε₁ ≠ ε₂`) have distinct pole
points at every prime `p`. -/
theorem polePoint_ne_of_ne {ε₁ ε₂ : ℝ} (hε₁ : ε₁ ≤ 1 / 2) (hε₂ : ε₂ ≤ 1 / 2)
    (hne : ε₁ ≠ ε₂) {p : ℕ} (hp : p.Prime) :
    (polePoint ε₁ hε₁).ω p ≠ (polePoint ε₂ hε₂).ω p := by
  intro heq
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hre : ((polePoint ε₁ hε₁).ω p).re = (p : ℝ) ^ (ε₁ - 1 / 2) ∧
      ((polePoint ε₂ hε₂).ω p).re = (p : ℝ) ^ (ε₂ - 1 / 2) := by
    simp only [polePoint, halfPlanePoint, if_neg hp.ne_zero]
    have hcast : ∀ ε : ℝ, ((1 / 2 : ℝ) : ℂ) - ((1 - ε : ℝ) : ℂ) = ((ε - 1 / 2 : ℝ) : ℂ) :=
      fun ε => by push_cast; ring
    rw [hcast, hcast, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow hp_pos.le,
      ← Complex.ofReal_cpow hp_pos.le, Complex.ofReal_re, Complex.ofReal_re]
    exact ⟨rfl, rfl⟩
  have hrpow : (p : ℝ) ^ (ε₁ - 1 / 2) = (p : ℝ) ^ (ε₂ - 1 / 2) := by
    rw [← hre.1, ← hre.2, heq]
  have hlog := congrArg Real.log hrpow
  rw [Real.log_rpow hp_pos, Real.log_rpow hp_pos] at hlog
  have hlog_ne : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have := mul_right_cancel₀ hlog_ne hlog
  exact hne (by linarith)

/-- **Smooth powers at distinct exponents `ε₁ ≠ ε₂` lie in strictly incomparable `WienerMonoidOrbit`
cones and have disjoint obstruction hulls.** -/
theorem not_wienerMonoidOrbit_smoothPower_of_ne {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₁2 : ε₁ < 1 / 2)
    (hε₂ : 0 < ε₂) (hε₂2 : ε₂ < 1 / 2) (hne : ε₁ ≠ ε₂) :
    Disjoint (obstructionHull (dampedSignWeight unitSign ε₁) (summable_abs_smoothPower_div hε₁))
      (obstructionHull (dampedSignWeight unitSign ε₂) (summable_abs_smoothPower_div hε₂)) ∧
    ¬ WienerMonoidOrbit (dampedSignWeight unitSign ε₁) (dampedSignWeight unitSign ε₂) ∧
    ¬ WienerMonoidOrbit (dampedSignWeight unitSign ε₂) (dampedSignWeight unitSign ε₁) := by
  have hdisj : Disjoint
      (obstructionHull (dampedSignWeight unitSign ε₁) (summable_abs_smoothPower_div hε₁))
      (obstructionHull (dampedSignWeight unitSign ε₂) (summable_abs_smoothPower_div hε₂)) := by
    rw [Set.disjoint_left]
    intro ω h₁ h₂
    have hp₁ := (mem_obstructionHull_smoothPower_iff hε₁ hε₁2 ω).1 h₁ 2 Nat.prime_two
    have hp₂ := (mem_obstructionHull_smoothPower_iff hε₂ hε₂2 ω).1 h₂ 2 Nat.prime_two
    exact polePoint_ne_of_ne hε₁2.le hε₂2.le hne Nat.prime_two (hp₁.symm.trans hp₂)
  have hnot12 : ¬ WienerMonoidOrbit (dampedSignWeight unitSign ε₁)
      (dampedSignWeight unitSign ε₂) := by
    intro h12
    have hsub := obstructionHull_subset_of_wienerMonoidOrbit
      (summable_abs_smoothPower_div hε₁) (summable_abs_smoothPower_div hε₂) h12
    have hmem₂ : polePoint ε₂ hε₂2.le ∈
        obstructionHull (dampedSignWeight unitSign ε₂) (summable_abs_smoothPower_div hε₂) :=
      (mem_obstructionHull_smoothPower_iff hε₂ hε₂2 _).2 fun _ _ => rfl
    exact Set.disjoint_left.1 hdisj (hsub hmem₂) hmem₂
  have hnot21 : ¬ WienerMonoidOrbit (dampedSignWeight unitSign ε₂)
      (dampedSignWeight unitSign ε₁) := by
    intro h21
    have hsub := obstructionHull_subset_of_wienerMonoidOrbit
      (summable_abs_smoothPower_div hε₂) (summable_abs_smoothPower_div hε₁) h21
    have hmem₁ : polePoint ε₁ hε₁2.le ∈
        obstructionHull (dampedSignWeight unitSign ε₁) (summable_abs_smoothPower_div hε₁) :=
      (mem_obstructionHull_smoothPower_iff hε₁ hε₁2 _).2 fun _ _ => rfl
    exact Set.disjoint_left.1 hdisj hmem₁ (hsub hmem₁)
  exact ⟨hdisj, hnot12, hnot21⟩

/-- **The smooth power `d^{−ε}` and the oscillating probe `d^{−ε} cos(t log d)` (`t ≠ 0`,
`ζ(1 − ε + it) ≠ 0`) lie in strictly incomparable `WienerMonoidOrbit` cones and have disjoint
obstruction hulls.** -/
theorem not_wienerMonoidOrbit_smoothPower_oscillating {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {t : ℝ} (ht : t ≠ 0) (hz : riemannZeta (oscillationExponent ε t) ≠ 0) :
    Disjoint (obstructionHull (dampedSignWeight unitSign ε) (summable_abs_smoothPower_div hε))
      (obstructionHull (oscillatingSmoothPower ε t)
        (summable_abs_oscillatingSmoothPower_div hε t)) ∧
    ¬ WienerMonoidOrbit (dampedSignWeight unitSign ε) (oscillatingSmoothPower ε t) ∧
    ¬ WienerMonoidOrbit (oscillatingSmoothPower ε t) (dampedSignWeight unitSign ε) := by
  have hdisj : Disjoint
      (obstructionHull (dampedSignWeight unitSign ε) (summable_abs_smoothPower_div hε))
      (obstructionHull (oscillatingSmoothPower ε t)
        (summable_abs_oscillatingSmoothPower_div hε t)) := by
    rw [Set.disjoint_left]
    intro ω h₁ h₂
    have hp₁ := (mem_obstructionHull_smoothPower_iff hε hε2 ω).1 h₁
    rcases (mem_obstructionHull_oscillating_iff hε hε2 hz ω).1 h₂ with hp₂ | hp₂
    · have h2 := (hp₁ 2 Nat.prime_two).symm.trans (hp₂ 2 Nat.prime_two)
      have h3 := (hp₁ 3 Nat.prime_three).symm.trans (hp₂ 3 Nat.prime_three)
      have heq := eq_of_halfPlanePoint_two_three (by simp; linarith)
        (half_le_re_oscillationExponent hε2 t) h2 h3
      have him := congrArg Complex.im heq
      simp [oscillationExponent] at him
      exact ht him.symm
    · have h2 := (hp₁ 2 Nat.prime_two).symm.trans (hp₂ 2 Nat.prime_two)
      have h3 := (hp₁ 3 Nat.prime_three).symm.trans (hp₂ 3 Nat.prime_three)
      have heq := eq_of_halfPlanePoint_two_three (by simp; linarith)
        (half_le_re_conj_oscillationExponent hε2 t) h2 h3
      have him := congrArg Complex.im heq
      simp [oscillationExponent] at him
      exact ht him
  have hnot12 : ¬ WienerMonoidOrbit (dampedSignWeight unitSign ε) (oscillatingSmoothPower ε t) := by
    intro h12
    have hsub := obstructionHull_subset_of_wienerMonoidOrbit
      (summable_abs_smoothPower_div hε) (summable_abs_oscillatingSmoothPower_div hε t) h12
    have hmem₂ : oscPoint ε t hε2 ∈
        obstructionHull (oscillatingSmoothPower ε t)
          (summable_abs_oscillatingSmoothPower_div hε t) :=
      (mem_obstructionHull_oscillating_iff hε hε2 hz _).2 (Or.inl fun _ _ => rfl)
    exact Set.disjoint_left.1 hdisj (hsub hmem₂) hmem₂
  have hnot21 : ¬ WienerMonoidOrbit (oscillatingSmoothPower ε t) (dampedSignWeight unitSign ε) := by
    intro h21
    have hsub := obstructionHull_subset_of_wienerMonoidOrbit
      (summable_abs_oscillatingSmoothPower_div hε t) (summable_abs_smoothPower_div hε) h21
    have hmem₁ : polePoint ε hε2.le ∈
        obstructionHull (dampedSignWeight unitSign ε) (summable_abs_smoothPower_div hε) :=
      (mem_obstructionHull_smoothPower_iff hε hε2 _).2 fun _ _ => rfl
    exact Set.disjoint_left.1 hdisj hmem₁ (hsub hmem₁)
  exact ⟨hdisj, hnot12, hnot21⟩

/-- **Master Synthesis for Open Problem 5 (`orbitStructure_of_unpaidClass_synthesis`):**
1. *Unit-orbit invariance and monoid-orbit monotonicity:* `WienerUnitOrbit` is an equivalence
   relation preserving `ReceiverBounded`, `paidIdeal`, `obstructionHull`, and quotient codimension
   (`Module.rank` / `Module.finrank`); along `WienerMonoidOrbit`, `paidIdeal` ascends,
   `obstructionHull` descends, `Module.rank` descends, and the paid class is the forward sink.
2. *Stabilizer–annihilator dichotomy:* on any single-point Bohr ideal `ker(ω₀)` (and on the
   conjugate-pair probe `oscillatingSmoothPower ε t` under real kernels), convolution by any
   `CriticalWiener k₀` either repairs the weight completely (`paidIdeal = ⊤`, `finrank = 0`) or
   preserves `paidIdeal`, `obstructionHull`, and `finrank` (`1` or `2`) identically.
3. *Infinite strictly descending monoid chains inside a single obstruction hull:* for `0 < ε < 1/2`,
   the iterated three-term convolutions `iterThreeTermConv m (d^{−ε})` (`m : ℕ`) all have the exact
   same `paidIdeal = ker(polePoint ε)`, `obstructionHull = {polePoint ε}`, and `finrank = 1`, while
   forming a strictly descending chain in `WienerMonoidOrbit` with pairwise distinct unit orbits.
4. *One-way orientation transition on the Möbius receiver and incomparable cones:* on
   `pmPowerDampedRealWeight ε` (`0 < ε ≤ 1/2`), `evenFlip` is a one-way monoid transition outside
   the unit orbit, while `d^{−ε₁}` (`ε₁ ≠ ε₂`) and `oscillatingSmoothPower ε t` (`t ≠ 0`,
   `ζ(1 − ε + it) ≠ 0`) lie in strictly incomparable `WienerMonoidOrbit` cones. -/
theorem orbitStructure_of_unpaidClass_synthesis {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    Equivalence WienerUnitOrbit ∧
    (∀ m : ℕ,
      ¬ ReceiverBounded (iterThreeTermConv m (dampedSignWeight unitSign ε)) ∧
      paidIdeal (iterThreeTermConv m (dampedSignWeight unitSign ε))
        (summable_abs_iterThreeTermConv_div m (summable_abs_smoothPower_div hε)) =
        paidIdeal (dampedSignWeight unitSign ε) (summable_abs_smoothPower_div hε) ∧
      WienerMonoidOrbit (iterThreeTermConv m (dampedSignWeight unitSign ε))
        (iterThreeTermConv (m + 1) (dampedSignWeight unitSign ε)) ∧
      ¬ WienerMonoidOrbit (iterThreeTermConv (m + 1) (dampedSignWeight unitSign ε))
        (iterThreeTermConv m (dampedSignWeight unitSign ε))) ∧
    (WienerMonoidOrbit (pmPowerDampedRealWeight ε) (evenFlip (pmPowerDampedRealWeight ε)) ∧
      ¬ WienerMonoidOrbit (evenFlip (pmPowerDampedRealWeight ε)) (pmPowerDampedRealWeight ε) ∧
      ¬ WienerUnitOrbit (pmPowerDampedRealWeight ε) (evenFlip (pmPowerDampedRealWeight ε))) ∧
    (∀ {t : ℝ}, t ≠ 0 → riemannZeta (oscillationExponent ε t) ≠ 0 →
      ¬ WienerMonoidOrbit (dampedSignWeight unitSign ε) (oscillatingSmoothPower ε t) ∧
      ¬ WienerMonoidOrbit (oscillatingSmoothPower ε t) (dampedSignWeight unitSign ε)) :=
  ⟨equivalence_wienerUnitOrbit,
   fun m =>
    let h := iterThreeTermConv_smoothPower_chain hε hε2 m
    ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩,
   let hm := moebius_evenFlip_oneWay_orbit hε hε2.le
   ⟨hm.2.1, hm.2.2.1, hm.2.2.2⟩,
   fun ht hz =>
    let ho := not_wienerMonoidOrbit_smoothPower_oscillating hε hε2 ht hz
    ⟨ho.2.1, ho.2.2⟩⟩

end

end GaloisForLFunctions.ArithmeticOrientationTheory
