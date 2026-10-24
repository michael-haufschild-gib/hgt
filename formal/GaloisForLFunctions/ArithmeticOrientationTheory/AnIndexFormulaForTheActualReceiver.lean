import GaloisForLFunctions.ArithmeticOrientationTheory.TheOrbitStructureOfTheUnpaidClass
import GaloisForLFunctions.ArithmeticOrientationTheory.ObstructionHullsAreNotConfinedToTheHalfPlane
import GaloisForLFunctions.TransHorizonIncidenceMechanics.SmallDampingMoebiusAndLiouvilleCancellationLaws
import GaloisForLFunctions.TransHorizonIncidenceMechanics.AVanishingFiniteLocalFactorPaysAWeightPretendingToOne

/-!
# An index formula for the actual receiver

In Arithmetic Orientation Theory (§3.6⁗, Open Problem 9), the damped Möbius receiver
`μ_ε(d) = μ(d) d^{−ε}` (`pmPowerDampedRealWeight ε`, `0 < ε < 1/2`) has its translated off-line zero
obstructions in `obstructionHull (pmPowerDampedRealWeight ε)`: every zero `ρ` of `ζ` with
`1/2 + ε < Re ρ < 1` and `ζ(ρ − ε) ≠ 0` contributes the half-plane point `ρ − ε` to the obstruction
hull (`mem_obstructionHull_moebius_of_zero`), and the repairing ideal `paidIdeal (μ_ε)` has
codimension at least the number of such zeros (`card_le_rank_quotient_paidIdeal_moebius`).

Open Problem 9 asks for:
1. the **reverse inclusion** (repairing kernels off the zeros) and **exclusion of off-half-plane
   untied obstructions** (`¬ TiedAtTwoThree ω`, which occur for general weights such as
   `towerTwistedPower ε a`, `exists_obstruction_not_tied`), turning the inclusion
   `translatedOffLineZeroHull ε ⊆ obstructionHull (μ_ε)` into an exact equality and the inequality
   `|Z| ≤ rank 𝒲_{1/2}/P(μ_ε)` into an exact index formula; and
2. the **index formulas and obstruction hulls** for the actual multiplicative receivers across the
   pretentious trichotomy (Möbius `μ`, Liouville `λ`, real character `χ`, and `1`-pretentious
   multiplicative weights `f(p) = 1`).

This module establishes the complete resolution of Open Problem 9:

1. **Reverse inclusion, untied-obstruction exclusion, and exact index formula for `μ d^{−ε}` right of
   the zero width (§1):**
   - For any weight `c : ℕ → ℝ` with summable mean, `paidIdeal c hc = ⊤`,
     `obstructionHull c hc = ∅`, and `Module.rank ℂ (𝒲_{1/2} ⧸ paidIdeal c hc) = 0` are each
     equivalent to `ReceiverBounded c` (`paidIdeal_eq_top_iff_receiverBounded`,
     `obstructionHull_eq_empty_iff_receiverBounded`,
     `rank_quotient_paidIdeal_eq_zero_iff_receiverBounded`).
   - Define `translatedOffLineZeroHull ε : Set BohrPoint`, the set of Bohr points agreeing at all
     primes with `halfPlanePoint (1/2) (ρ − ε)` for some zero `ρ` of `ζ` with `1/2 + ε < Re ρ < 1`
     and `ζ(ρ − ε) ≠ 0`. For every `0 < ε < 1/2`,
     `translatedOffLineZeroHull ε ⊆ obstructionHull (pmPowerDampedRealWeight ε)` and every point of
     `translatedOffLineZeroHull ε` satisfies the half-plane radius tie `TiedAtTwoThree`
     (`translatedOffLineZeroHull_subset_obstructionHull_moebius`,
     `tiedAtTwoThree_of_mem_translatedOffLineZeroHull`).
   - Right of the zero width (`zetaZeroAbscissa − 1/2 < ε < 1/2`), Mellin–Hardy inversion on
     `(1 − 2^{1−s}) ζ(s) / (s ζ(s + ε))` (`receiverBounded_moebius_of_zetaZeroAbscissa_sub_half_lt`)
     proves the **exact reverse inclusion and zero-codimension index formula**
     (`moebius_reverse_inclusion_and_index_above_zeroWidth`):
     - `paidIdeal (pmPowerDampedRealWeight ε) = ⊤` (every `k ∈ 𝒲_{1/2}` repairs `μ d^{−ε}`);
     - `obstructionHull (pmPowerDampedRealWeight ε) = translatedOffLineZeroHull ε` and both equal `∅`
       (in particular, **every** off-half-plane untied Bohr point `¬ TiedAtTwoThree ω` is excluded
       from `obstructionHull (pmPowerDampedRealWeight ε)`, in sharp contrast to
       `towerTwistedPower ε a`);
     - `Module.rank ℂ (𝒲_{1/2} ⧸ paidIdeal (pmPowerDampedRealWeight ε)) = 0` and
       `Module.finrank ℂ (𝒲_{1/2} ⧸ paidIdeal (pmPowerDampedRealWeight ε)) = 0`.
   - Across the entire sub-half damping strip `0 < ε < 1/2`, the global reverse inclusion and index
     formula form an exact equivalence with `RiemannHypothesis` (`moebius_reverse_inclusion_and_index_tfae`).

2. **Exact Wiener-unit orbit and identical index invariants of the Möbius and Liouville receivers (§2):**
   - For every `ε > 0`, the damped square-indicator kernel `dampedSignWeight RHTower.squareIndicatorR ε`
     (`1_□(q) q^{−ε}`) and its square-dilated Möbius inverse `dampedSignWeight squareMoebius ε`
     (`μ(√q) 1_□(q) q^{−ε}`) are **units of the critical Wiener monoid** (`IsWienerUnit`,
     `isWienerUnit_dampedSquare`, `isWienerUnit_dampedSquareMoebius`).
   - Consequently, the Liouville receiver `λ(d) d^{−ε}` and the Möbius receiver `μ(d) d^{−ε}` lie in
     the **exact same `WienerUnitOrbit`** at every `ε > 0` (`wienerUnitOrbit_moebius_liouville`) and
     share the **identical** repairing ideal `paidIdeal`, **identical** obstruction hull
     `obstructionHull`, and **identical** quotient `Module.rank` and `Module.finrank`
     (`liouville_paidIdeal_obstructionHull_and_index_eq_moebius`).

3. **The multiplicative receiver trichotomy in `paidIdeal`, `obstructionHull`, and quotient
   codimension (§3):**
   - *Model `μ` (`f(p) = −1`, `|f| ≤ 1`):* `f d^{−ε} = ((f * ζ) d^{−ε}) ⋆ (μ d^{−ε})` with
     `(f * ζ) d^{−ε} ∈ CriticalWiener`, so `WienerMonoidOrbit (μ d^{−ε}) (f d^{−ε})`,
     `paidIdeal (μ d^{−ε}) ≤ paidIdeal (f d^{−ε})`,
     `obstructionHull (f d^{−ε}) ⊆ obstructionHull (μ d^{−ε})`, and
     `Module.rank ℂ (𝒲_{1/2} ⧸ paidIdeal (f d^{−ε})) ≤ Module.rank ℂ (𝒲_{1/2} ⧸ paidIdeal (μ d^{−ε}))`
     (`multiplicative_neg_one_monoidOrbit_and_index_le_moebius`), with `paidIdeal = ⊤`,
     `obstructionHull = ∅`, and `finrank = 0` for all `ε > zetaZeroAbscissa − 1/2`.
   - *Model `χ` (`f(p) = χ(p)` for non-principal real `χ`, `|f| ≤ 1`):* unconditionally for **every**
     `ε > 0`, `paidIdeal (f d^{−ε}) = ⊤`, `obstructionHull (f d^{−ε}) = ∅` (excluding all half-plane
     and off-half-plane obstructions unconditionally), `Module.rank = 0`, and `Module.finrank = 0`
     (`multiplicative_char_paidIdeal_obstructionHull_and_index`).
   - *Model `1` (`f(p) = 1`, `|f| ≤ B`):* `f d^{−ε} = ((f * μ) d^{−ε}) ⋆ d^{−ε}` with
     `(f * μ) d^{−ε} ∈ CriticalWiener` and pole evaluation `∑_n (f * μ)(n)/n = ∏_p (1 − p^{−1}) L_p`.
     By the stabilizer–annihilator dichotomy (`paidIdeal_conv_dichotomy_of_eq_ker`):
     - if no local factor `L_p = poleLocalFactor f p` vanishes (in particular for **every**
       multiplicative `f` with `f(p) = 1` and `|f| ≤ 1`), then for every `0 < ε < 1/2`:
       `paidIdeal (f d^{−ε}) = RingHom.ker (bohrCharacter (1/2) (polePoint ε))`,
       `obstructionHull (f d^{−ε}) = {ω | ∀ p, p.Prime → ω.ω p = (polePoint ε).ω p}`, and
       `Module.finrank ℂ (𝒲_{1/2} ⧸ paidIdeal (f d^{−ε})) = 1`
       (`multiplicative_one_paidIdeal_obstructionHull_and_index_of_poleLocalFactor_ne_zero`,
       `multiplicative_one_paidIdeal_obstructionHull_and_index_of_abs_le_one`);
     - if `f` has finite local factors (`f(p^k) = 0` for `k > K`), `f d^{−ε}` has codimension `0`
       (`paidIdeal = ⊤`, `obstructionHull = ∅`) if some `L_p = 0`, and codimension `1`
       (`paidIdeal = ker(polePoint ε)`, `obstructionHull = {polePoint ε}`) if every `L_p ≠ 0`
       (`multiplicative_one_finiteLocalFactor_index_dichotomy`).
-/

open Finset ArithmeticFunction LSeries Complex Filter Topology Set

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open TransHorizonIncidenceMechanics WienerAlgebraAt BezoutValuationIncidence _root_.RHTower

noncomputable section
set_option autoImplicit false

/-! ### §1. General zero-codimension characterizations and the translated off-line zero hull of `μ d^{−ε}` -/

/-- **A weight is paid if and only if its repairing ideal is the full critical Wiener algebra `⊤`.** -/
theorem paidIdeal_eq_top_iff_receiverBounded {c : ℕ → ℝ}
    (hc : Summable fun d : ℕ => |c d / d|) :
    paidIdeal c hc = ⊤ ↔ ReceiverBounded c := by
  rw [Ideal.eq_top_iff_one, one_mem_paidIdeal_iff]

/-- **A weight is paid if and only if its obstruction hull on the Bohr polydisk is empty.** -/
theorem obstructionHull_eq_empty_iff_receiverBounded {c : ℕ → ℝ}
    (hc : Summable fun d : ℕ => |c d / d|) :
    obstructionHull c hc = ∅ ↔ ReceiverBounded c := by
  rw [← Set.not_nonempty_iff_eq_empty, obstructionHull_nonempty_iff, not_not]

/-- **A weight is paid if and only if its repairing ideal has quotient rank `0`:**
if `c` is paid, `𝒲_{1/2} ⧸ paidIdeal c hc` is subsingleton (`rank = 0`, `finrank = 0`); if `c` is
unpaid, `obstructionHull c hc` contains a Bohr point `ω`, whose character surjects the quotient onto
`ℂ` (`1 ≤ rank`). -/
theorem rank_quotient_paidIdeal_eq_zero_iff_receiverBounded {c : ℕ → ℝ}
    (hc : Summable fun d : ℕ => |c d / d|) :
    Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸ paidIdeal c hc) = 0 ↔ ReceiverBounded c := by
  constructor
  · intro hrank
    by_contra hunpaid
    obtain ⟨ω, hω⟩ := (obstructionHull_nonempty_iff c hc).2 hunpaid
    have h1 := card_le_rank_quotient_of_separated
      (fun _ : Unit => WienerAlgebraAt.bohrCharacter (1 / 2) ω)
      (fun _ _ h => (h rfl).elim) (paidIdeal c hc) (fun k hk _ => hω k hk)
    rw [Fintype.card_unit, Nat.cast_one, hrank] at h1
    exact not_lt_of_ge h1 zero_lt_one
  · intro hpaid
    have htop : paidIdeal c hc = ⊤ := (paidIdeal_eq_top_iff_receiverBounded hc).2 hpaid
    rw [htop]
    haveI : Subsingleton (WienerAlgebraAt (1 / 2) ⧸ (⊤ : Ideal (WienerAlgebraAt (1 / 2)))) :=
      Ideal.Quotient.subsingleton_iff.2 rfl
    exact rank_subsingleton' _ _

/-- When `ReceiverBounded c`, `Module.finrank ℂ (𝒲_{1/2} ⧸ paidIdeal c hc) = 0`. -/
theorem finrank_quotient_paidIdeal_eq_zero_of_receiverBounded {c : ℕ → ℝ}
    (hc : Summable fun d : ℕ => |c d / d|) (hpaid : ReceiverBounded c) :
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸ paidIdeal c hc) = 0 := by
  rw [(paidIdeal_eq_top_iff_receiverBounded hc).2 hpaid]
  haveI : Subsingleton (WienerAlgebraAt (1 / 2) ⧸ (⊤ : Ideal (WienerAlgebraAt (1 / 2)))) :=
    Ideal.Quotient.subsingleton_iff.2 rfl
  exact Module.finrank_zero_of_subsingleton

/-- The **translated off-line zero hull** `translatedOffLineZeroHull ε` (`0 < ε < 1/2`): the set of
Bohr points `ω` agreeing at all primes with `halfPlanePoint (1/2) (ρ − ε)` for some off-line zero
`ρ` of `ζ` with `1/2 + ε < Re ρ < 1` and `ζ(ρ − ε) ≠ 0`. -/
def translatedOffLineZeroHull (ε : ℝ) : Set BohrPoint :=
  {ω : BohrPoint | ∃ (ρ : ℂ) (hρ : 1 / 2 + ε < ρ.re),
    ρ.re < 1 ∧ riemannZeta ρ = 0 ∧ riemannZeta (ρ - ε) ≠ 0 ∧
    ∀ p : ℕ, p.Prime →
      ω.ω p = (halfPlanePoint (1 / 2) (ρ - ε) (by simp; linarith)).ω p}

/-- **Forward inclusion (`translatedOffLineZeroHull_subset_obstructionHull_moebius`):**
For every `0 < ε < 1/2`, every Bohr point in `translatedOffLineZeroHull ε` lies in the obstruction
hull of the damped Möbius receiver `pmPowerDampedRealWeight ε`. -/
theorem translatedOffLineZeroHull_subset_obstructionHull_moebius {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    translatedOffLineZeroHull ε ⊆
      obstructionHull (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) := by
  rintro ω ⟨ρ, hρ, hρ1, hz, hz', hω⟩ k hk
  rw [bohrEval_congr k.toFn (BohrPoint.eq_of_primes hω)]
  exact mem_obstructionHull_moebius_of_zero hε hε2 hρ hρ1 hz hz' k hk

/-- **Every point of `translatedOffLineZeroHull ε` has tied radii at `2` and `3`
(`TiedAtTwoThree`):** off-half-plane untied Bohr points (`¬ TiedAtTwoThree ω`) never lie in
`translatedOffLineZeroHull ε`. -/
theorem tiedAtTwoThree_of_mem_translatedOffLineZeroHull {ε : ℝ} {ω : BohrPoint}
    (hω : ω ∈ translatedOffLineZeroHull ε) : TiedAtTwoThree ω := by
  obtain ⟨ρ, hρ, -, -, -, hp⟩ := hω
  have hre : (1 / 2 : ℝ) ≤ (ρ - ε).re := by simp; linarith
  have htied := tiedAtTwoThree_halfPlanePoint (ρ - ε) hre
  unfold TiedAtTwoThree at htied ⊢
  rw [hp 2 Nat.prime_two, hp 3 Nat.prime_three]
  exact htied

/-- **Exact Reverse Inclusion, Untied-Obstruction Exclusion, and Zero-Codimension Index Formula
for `μ d^{−ε}` Right of the Zero Width (`moebius_reverse_inclusion_and_index_above_zeroWidth`):**
For every damping `ε` with `zetaZeroAbscissa − 1/2 < ε < 1/2`:
1. `ReceiverBounded (pmPowerDampedRealWeight ε)` holds (`AdmissionBelowHalfDampingAboveTheZeroWidth`);
2. `paidIdeal (pmPowerDampedRealWeight ε) = ⊤` (every `k ∈ 𝒲_{1/2}` repairs `μ d^{−ε}`);
3. `obstructionHull (pmPowerDampedRealWeight ε) = translatedOffLineZeroHull ε` and both equal `∅`
   (establishing the reverse inclusion `obstructionHull (μ d^{−ε}) ⊆ translatedOffLineZeroHull ε`
   and excluding **all** off-half-plane untied Bohr points `¬ TiedAtTwoThree ω`);
4. `Module.rank ℂ (𝒲_{1/2} ⧸ paidIdeal (pmPowerDampedRealWeight ε)) = 0` and
   `Module.finrank ℂ (𝒲_{1/2} ⧸ paidIdeal (pmPowerDampedRealWeight ε)) = 0`. -/
theorem moebius_reverse_inclusion_and_index_above_zeroWidth {ε : ℝ}
    (hεΘ : zetaZeroAbscissa - 1 / 2 < ε) (hε2 : ε < 1 / 2) :
    have hε : 0 < ε := by linarith [half_le_zetaZeroAbscissa]
    ReceiverBounded (pmPowerDampedRealWeight ε) ∧
    paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) = ⊤ ∧
    obstructionHull (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) =
      translatedOffLineZeroHull ε ∧
    translatedOffLineZeroHull ε = ∅ ∧
    (∀ ω ∈ obstructionHull (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε),
      TiedAtTwoThree ω) ∧
    Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸
      paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε)) = 0 ∧
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
      paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε)) = 0 := by
  have hε : 0 < ε := by linarith [half_le_zetaZeroAbscissa]
  have hpaid : ReceiverBounded (pmPowerDampedRealWeight ε) :=
    receiverBounded_moebius_of_zetaZeroAbscissa_sub_half_lt hεΘ
  have htop : paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) = ⊤ :=
    (paidIdeal_eq_top_iff_receiverBounded (summable_abs_moebius_div hε)).2 hpaid
  have hhull : obstructionHull (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) = ∅ :=
    (obstructionHull_eq_empty_iff_receiverBounded (summable_abs_moebius_div hε)).2 hpaid
  have htrans : translatedOffLineZeroHull ε = ∅ :=
    Set.subset_eq_empty (translatedOffLineZeroHull_subset_obstructionHull_moebius hε hε2) hhull
  exact ⟨hpaid, htop, hhull.trans htrans.symm, htrans,
    fun ω hω => False.elim (by rw [hhull] at hω; exact hω),
    (rank_quotient_paidIdeal_eq_zero_iff_receiverBounded (summable_abs_moebius_div hε)).2 hpaid,
    finrank_quotient_paidIdeal_eq_zero_of_receiverBounded (summable_abs_moebius_div hε) hpaid⟩

/-- **Arithmetic Selectivity of the Möbius Obstruction Hull Against Tower-Twisted Smooth Powers
(`moebius_vs_towerTwisted_obstructionHull_selectivity`):**
For every `ε` with `zetaZeroAbscissa − 1/2 < ε < 1/2`, there exists a tower parameter
`a ∈ (2^{1−ε}, 2)` such that `towerTwistedPower ε a` has an untied off-half-plane obstruction
`ω ∈ obstructionHull (towerTwistedPower ε a)` with `¬ TiedAtTwoThree ω`, whereas
`obstructionHull (pmPowerDampedRealWeight ε) = translatedOffLineZeroHull ε = ∅` contains no untied
(or tied) obstructions at all. -/
theorem moebius_vs_towerTwisted_obstructionHull_selectivity {ε : ℝ}
    (hεΘ : zetaZeroAbscissa - 1 / 2 < ε) (hε2 : ε < 1 / 2) :
    have hε : 0 < ε := by linarith [half_le_zetaZeroAbscissa]
    (∃ a : ℝ, ∃ (ha1 : (2 : ℝ) ^ (1 - ε) < a) (ha2 : a < 2),
      ∃ ω ∈ obstructionHull (towerTwistedPower ε a) (summable_abs_towerTwisted_div' hε ha1 ha2),
        ¬ TiedAtTwoThree ω ∧
        ω ∉ obstructionHull (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε)) := by
  have hε : 0 < ε := by linarith [half_le_zetaZeroAbscissa]
  obtain ⟨a, ha1, ha2, ω, hω, hnot⟩ := exists_obstruction_not_tied hε hε2
  have hhull := (moebius_reverse_inclusion_and_index_above_zeroWidth hεΘ hε2).2.2.1.trans
    (moebius_reverse_inclusion_and_index_above_zeroWidth hεΘ hε2).2.2.2.1
  refine ⟨a, ha1, ha2, ω, hω, hnot, ?_⟩
  rw [hhull]
  exact Set.notMem_empty ω

/-- **All-Damping Reverse Inclusion and Index Equivalence for the Möbius Receiver
(`moebius_reverse_inclusion_and_index_tfae`):**
Across the sub-half damping strip `0 < ε < 1/2`, the following are equivalent:
1. `RiemannHypothesis`;
2. `zetaZeroAbscissa = 1 / 2`;
3. `∀ ε : ℝ, 0 < ε → ε < 1 / 2 → paidIdeal (pmPowerDampedRealWeight ε) = ⊤`;
4. `∀ ε : ℝ, 0 < ε → ε < 1 / 2 → obstructionHull (pmPowerDampedRealWeight ε) = ∅`;
5. `∀ ε : ℝ, 0 < ε → ε < 1 / 2 → obstructionHull (pmPowerDampedRealWeight ε) = translatedOffLineZeroHull ε ∧ translatedOffLineZeroHull ε = ∅`;
6. `∀ ε : ℝ, 0 < ε → ε < 1 / 2 → Module.rank ℂ (𝒲_{1/2} ⧸ paidIdeal (pmPowerDampedRealWeight ε)) = 0`. -/
theorem moebius_reverse_inclusion_and_index_tfae : List.TFAE [
    RiemannHypothesis,
    zetaZeroAbscissa = 1 / 2,
    ∀ ε : ℝ, ∀ (hε : 0 < ε), ε < 1 / 2 →
      paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) = ⊤,
    ∀ ε : ℝ, ∀ (hε : 0 < ε), ε < 1 / 2 →
      obstructionHull (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) = ∅,
    ∀ ε : ℝ, ∀ (hε : 0 < ε), ε < 1 / 2 →
      obstructionHull (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) =
        translatedOffLineZeroHull ε ∧ translatedOffLineZeroHull ε = ∅,
    ∀ ε : ℝ, ∀ (hε : 0 < ε), ε < 1 / 2 →
      Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε)) = 0] := by
  tfae_have 1 ↔ 2 := zetaZeroAbscissa_eq_half_iff_riemannHypothesis.symm
  tfae_have 2 → 5 := by
    intro hΘ ε hε hε2
    have h := moebius_reverse_inclusion_and_index_above_zeroWidth (by linarith) hε2
    exact ⟨h.2.2.1, h.2.2.2.1⟩
  tfae_have 5 → 4 := fun h ε hε hε2 => (h ε hε hε2).1.trans (h ε hε hε2).2
  tfae_have 4 ↔ 3 := by
    refine forall_congr' fun ε => forall_congr' fun hε => imp_congr_right fun _ => ?_
    rw [obstructionHull_eq_empty_iff_receiverBounded, paidIdeal_eq_top_iff_receiverBounded]
  tfae_have 3 ↔ 6 := by
    refine forall_congr' fun ε => forall_congr' fun hε => imp_congr_right fun _ => ?_
    rw [paidIdeal_eq_top_iff_receiverBounded, rank_quotient_paidIdeal_eq_zero_iff_receiverBounded]
  tfae_have 3 → 1 := by
    intro h
    rw [riemannHypothesis_iff_forall_pos_receiverBounded_moebius]
    intro ε hε
    rcases lt_or_ge ε (1 / 2) with hε2 | hε2
    · exact (paidIdeal_eq_top_iff_receiverBounded (summable_abs_moebius_div hε)).1 (h ε hε hε2)
    · exact (mem_receiverDampings_iff_receiverBounded hε).mp (Ici_half_subset_receiverDampings hε2)
  tfae_finish

/-! ### §2. Exact Wiener-unit orbit and identical index invariants of the Möbius and Liouville receivers -/

/-- **The damped square-indicator kernel `1_□(q) q^{−ε}` is a unit of the critical Wiener monoid
for every `ε > 0`.** Its Dirichlet inverse is the damped square-dilated Möbius kernel
`μ(√q) 1_□(q) q^{−ε}`. -/
theorem isWienerUnit_dampedSquare {ε : ℝ} (hε : 0 < ε) :
    IsWienerUnit (dampedSignWeight RHTower.squareIndicatorR ε) := by
  have hm1 : pmPowerDampedRealWeight ε 1 ≠ 0 := by
    unfold pmPowerDampedRealWeight moebiusReal
    simp
  rw [← wienerMonoidOrbit_conv_self_iff hm1 (criticalWiener_dampedSquare hε)]
  refine ⟨dampedSignWeight squareMoebius ε, criticalWiener_dampedSquareMoebius hε, fun n _ => ?_⟩
  rw [dampedMoebius_eq_dirichletConv ε n]
  exact dirichletConv_congr (fun _ _ => rfl) (fun m _ => dampedLiouville_eq_dirichletConv ε m) n

/-- **The damped square-dilated Möbius kernel `μ(√q) 1_□(q) q^{−ε}` is a unit of the critical
Wiener monoid for every `ε > 0`.** -/
theorem isWienerUnit_dampedSquareMoebius {ε : ℝ} (hε : 0 < ε) :
    IsWienerUnit (dampedSignWeight squareMoebius ε) := by
  obtain ⟨h1, g, hg, hconv⟩ := isWienerUnit_dampedSquare hε
  have hmem : WienerMonoidOrbit (pmPowerDampedRealWeight ε)
      (dampedSignWeight RHTower.liouvilleR ε) :=
    ⟨dampedSignWeight RHTower.squareIndicatorR ε, h1, fun n _ => dampedLiouville_eq_dirichletConv ε n⟩
  have hself : WienerMonoidOrbit
      (RHTower.dirichletConv (dampedSignWeight squareMoebius ε)
        (dampedSignWeight RHTower.liouvilleR ε))
      (dampedSignWeight RHTower.liouvilleR ε) := by
    obtain ⟨k, hk, hc⟩ := hmem
    refine ⟨k, hk, fun n hn => ?_⟩
    rw [hc n hn]
    exact dirichletConv_congr (fun _ _ => rfl) (fun m _ => dampedMoebius_eq_dirichletConv ε m) n
  have hliouv1 : dampedSignWeight RHTower.liouvilleR ε 1 ≠ 0 := by
    have h1 : RHTower.liouvilleR 1 ≠ 0 := by
      have habs := abs_liouvilleR one_ne_zero
      intro h0
      rw [h0, abs_zero] at habs
      norm_num at habs
    simpa [dampedSignWeight] using h1
  exact (wienerMonoidOrbit_conv_self_iff hliouv1 (criticalWiener_dampedSquareMoebius hε)).1 hself

/-- **The Möbius receiver `μ(d) d^{−ε}` and the Liouville receiver `λ(d) d^{−ε}` lie in the exact
same `WienerUnitOrbit` for every `ε > 0`.** -/
theorem wienerUnitOrbit_moebius_liouville {ε : ℝ} (hε : 0 < ε) :
    WienerUnitOrbit (pmPowerDampedRealWeight ε) (dampedSignWeight RHTower.liouvilleR ε) :=
  ⟨dampedSignWeight RHTower.squareIndicatorR ε, isWienerUnit_dampedSquare hε,
    fun n _ => dampedLiouville_eq_dirichletConv ε n⟩

/-- **Identical Repairing Ideals, Obstruction Hulls, and Quotient Codimensions for the Liouville
and Möbius Receivers (`liouville_paidIdeal_obstructionHull_and_index_eq_moebius`):**
For every `ε > 0`:
1. `paidIdeal (λ d^{−ε}) = paidIdeal (μ d^{−ε})`;
2. `obstructionHull (λ d^{−ε}) = obstructionHull (μ d^{−ε})`;
3. `Module.rank ℂ (𝒲_{1/2} ⧸ paidIdeal (λ d^{−ε})) = Module.rank ℂ (𝒲_{1/2} ⧸ paidIdeal (μ d^{−ε}))`
   and `Module.finrank ℂ (𝒲_{1/2} ⧸ paidIdeal (λ d^{−ε})) = Module.finrank ℂ (𝒲_{1/2} ⧸ paidIdeal (μ d^{−ε}))`;
4. for `0 < ε < 1/2` and any finite set `Z` of zeros of `ζ` with `1/2 + ε < Re ρ < 1` and
   `ζ(ρ − ε) ≠ 0`, `translatedOffLineZeroHull ε ⊆ obstructionHull (λ d^{−ε})` and
   `|Z| ≤ Module.rank ℂ (𝒲_{1/2} ⧸ paidIdeal (λ d^{−ε}))`;
5. for `zetaZeroAbscissa − 1/2 < ε < 1/2`, `obstructionHull (λ d^{−ε}) = translatedOffLineZeroHull ε = ∅`,
   `paidIdeal (λ d^{−ε}) = ⊤`, and `Module.finrank ℂ (𝒲_{1/2} ⧸ paidIdeal (λ d^{−ε})) = 0`. -/
theorem liouville_paidIdeal_obstructionHull_and_index_eq_moebius {ε : ℝ} (hε : 0 < ε) :
    paidIdeal (dampedSignWeight RHTower.liouvilleR ε) (summable_abs_dampedLiouville_div hε) =
      paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) ∧
    obstructionHull (dampedSignWeight RHTower.liouvilleR ε) (summable_abs_dampedLiouville_div hε) =
      obstructionHull (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) ∧
    Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (dampedSignWeight RHTower.liouvilleR ε) (summable_abs_dampedLiouville_div hε)) =
      Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε)) ∧
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (dampedSignWeight RHTower.liouvilleR ε) (summable_abs_dampedLiouville_div hε)) =
      Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε)) ∧
    (ε < 1 / 2 →
      translatedOffLineZeroHull ε ⊆
        obstructionHull (dampedSignWeight RHTower.liouvilleR ε)
          (summable_abs_dampedLiouville_div hε) ∧
      ∀ (Z : Finset ℂ),
        (∀ ρ ∈ Z, 1 / 2 + ε < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧ riemannZeta (ρ - ε) ≠ 0) →
        (Z.card : Cardinal) ≤ Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸
          paidIdeal (dampedSignWeight RHTower.liouvilleR ε)
            (summable_abs_dampedLiouville_div hε))) ∧
    (zetaZeroAbscissa - 1 / 2 < ε → ε < 1 / 2 →
      paidIdeal (dampedSignWeight RHTower.liouvilleR ε) (summable_abs_dampedLiouville_div hε) = ⊤ ∧
      obstructionHull (dampedSignWeight RHTower.liouvilleR ε)
        (summable_abs_dampedLiouville_div hε) = translatedOffLineZeroHull ε ∧
      Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (dampedSignWeight RHTower.liouvilleR ε)
          (summable_abs_dampedLiouville_div hε)) = 0) := by
  have horb := wienerUnitOrbit_symm (wienerUnitOrbit_moebius_liouville hε)
  have hid := paidIdeal_eq_of_wienerUnitOrbit (summable_abs_dampedLiouville_div hε)
    (summable_abs_moebius_div hε) horb
  have hhull := obstructionHull_eq_of_wienerUnitOrbit (summable_abs_dampedLiouville_div hε)
    (summable_abs_moebius_div hε) horb
  have hrank := rank_quotient_paidIdeal_eq_of_wienerUnitOrbit (summable_abs_dampedLiouville_div hε)
    (summable_abs_moebius_div hε) horb
  refine ⟨hid, hhull, hrank.1, hrank.2, fun hε2 => ?_, fun hεΘ hε2 => ?_⟩
  · rw [hhull, hrank.1]
    exact ⟨translatedOffLineZeroHull_subset_obstructionHull_moebius hε hε2,
      card_le_rank_quotient_paidIdeal_moebius hε hε2⟩
  · have hm := moebius_reverse_inclusion_and_index_above_zeroWidth hεΘ hε2
    rw [hrank.2, hid, hhull]
    exact ⟨hm.2.1, hm.2.2.1, hm.2.2.2.2.2.2⟩

/-! ### §3. The multiplicative receiver trichotomy in `paidIdeal`, `obstructionHull`, and quotient codimension -/

/-- **1. Möbius-pretentious multiplicative weights (`f(p) = −1`, `|f| ≤ 1`):**
Every multiplicative `f` with `f(p) = −1` at all primes and `|f| ≤ 1` lies in the forward critical
Wiener monoid orbit of `pmPowerDampedRealWeight ε`, so:
- `paidIdeal (μ d^{−ε}) ≤ paidIdeal (f d^{−ε})`,
- `obstructionHull (f d^{−ε}) ⊆ obstructionHull (μ d^{−ε})`,
- `Module.rank ℂ (𝒲_{1/2} ⧸ paidIdeal (f d^{−ε})) ≤ Module.rank ℂ (𝒲_{1/2} ⧸ paidIdeal (μ d^{−ε}))`,
and for `ε > zetaZeroAbscissa − 1/2` (and unconditionally at `ε = 1/2`), `paidIdeal (f d^{−ε}) = ⊤`,
`obstructionHull (f d^{−ε}) = ∅`, and `Module.finrank ℂ (𝒲_{1/2} ⧸ paidIdeal (f d^{−ε})) = 0`. -/
theorem multiplicative_neg_one_monoidOrbit_and_index_le_moebius {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hfp : ∀ p : ℕ, p.Prime → f p = -1) (hbd : ∀ n, |f n| ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    WienerMonoidOrbit (pmPowerDampedRealWeight ε) (dampedSignWeight ⇑f ε) ∧
    paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) ≤
      paidIdeal (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le hbd hε) ∧
    obstructionHull (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le hbd hε) ⊆
      obstructionHull (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) ∧
    Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le hbd hε)) ≤
      Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε)) ∧
    (zetaZeroAbscissa - 1 / 2 < ε →
      paidIdeal (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le hbd hε) = ⊤ ∧
      obstructionHull (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le hbd hε) = ∅ ∧
      Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le hbd hε)) = 0) := by
  have horb : WienerMonoidOrbit (pmPowerDampedRealWeight ε) (dampedSignWeight ⇑f ε) :=
    ⟨dampedSignWeight ⇑(f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ε,
      criticalWiener_mul_zeta hf hfp hbd hε, fun n _ => dampedMultiplicative_eq_dirichletConv f ε n⟩
  have hsf := summable_abs_dampedSign_div_of_abs_le hbd hε
  have hsm := summable_abs_moebius_div hε
  refine ⟨horb, paidIdeal_le_of_wienerMonoidOrbit hsm hsf horb,
    obstructionHull_subset_of_wienerMonoidOrbit hsm hsf horb,
    rank_quotient_paidIdeal_le_of_wienerMonoidOrbit hsm hsf horb, fun hεΘ => ?_⟩
  have hpaid : ReceiverBounded (dampedSignWeight ⇑f ε) :=
    receiverBounded_of_primes_neg_one hf hfp hbd hε
      (receiverBounded_moebius_of_zetaZeroAbscissa_sub_half_lt hεΘ)
  exact ⟨(paidIdeal_eq_top_iff_receiverBounded hsf).2 hpaid,
    (obstructionHull_eq_empty_iff_receiverBounded hsf).2 hpaid,
    finrank_quotient_paidIdeal_eq_zero_of_receiverBounded hsf hpaid⟩

/-- **2. Character-pretentious multiplicative weights (`f(p) = χ(p)` for non-principal real `χ`,
`|f| ≤ 1`):**
Unconditionally at **every** damping `ε > 0`, `f(d) d^{−ε}` has:
- `ReceiverBounded (dampedSignWeight ⇑f ε)`,
- `paidIdeal (dampedSignWeight ⇑f ε) = ⊤`,
- `obstructionHull (dampedSignWeight ⇑f ε) = ∅` (excluding all half-plane and off-half-plane
  obstructions unconditionally),
- `Module.rank ℂ (𝒲_{1/2} ⧸ paidIdeal (dampedSignWeight ⇑f ε)) = 0` and
  `Module.finrank ℂ (𝒲_{1/2} ⧸ paidIdeal (dampedSignWeight ⇑f ε)) = 0`. -/
theorem multiplicative_char_paidIdeal_obstructionHull_and_index {q : ℕ} [NeZero q]
    {χ : MulChar (ZMod q) ℤ} (hχ : χ ≠ 1) {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hbd : ∀ n, |f n| ≤ 1)
    (hfp : ∀ p : ℕ, p.Prime → f p = charSign χ p) {ε : ℝ} (hε : 0 < ε) :
    ReceiverBounded (dampedSignWeight ⇑f ε) ∧
    paidIdeal (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le hbd hε) = ⊤ ∧
    obstructionHull (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le hbd hε) = ∅ ∧
    Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸
      paidIdeal (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le hbd hε)) = 0 ∧
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
      paidIdeal (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le hbd hε)) = 0 := by
  have hpaid := receiverBounded_of_primes_char hχ hf hbd hfp hε
  have hsf := summable_abs_dampedSign_div_of_abs_le hbd hε
  exact ⟨hpaid, (paidIdeal_eq_top_iff_receiverBounded hsf).2 hpaid,
    (obstructionHull_eq_empty_iff_receiverBounded hsf).2 hpaid,
    (rank_quotient_paidIdeal_eq_zero_iff_receiverBounded hsf).2 hpaid,
    finrank_quotient_paidIdeal_eq_zero_of_receiverBounded hsf hpaid⟩

/-- Summability of `|dampedSignWeight f ε d / d|` when `|f n| ≤ B`. -/
theorem summable_abs_dampedSign_div_of_abs_le_const {f : ℕ → ℝ} {B : ℝ}
    (hB : ∀ n, |f n| ≤ B) {ε : ℝ} (hε : 0 < ε) :
    Summable fun d : ℕ => |dampedSignWeight f ε d / d| := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 1)
  refine ((Real.summable_nat_rpow.mpr (show -(1 + ε) < -1 by linarith)).mul_left B).of_nonneg_of_le
    (fun _ => abs_nonneg _) fun d => ?_
  rw [dampedSignWeight_div hε, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _),
    mul_comm]
  exact mul_le_mul_of_nonneg_right (hB d) (Real.rpow_nonneg (Nat.cast_nonneg d) _)

/-- **3A. `1`-pretentious multiplicative weights (`f(p) = 1`, `|f| ≤ B`) with nonvanishing local
factors (`∀ p, p.Prime → poleLocalFactor f p ≠ 0`):**
Writing `f d^{−ε} = ((f * μ) d^{−ε}) ⋆ d^{−ε}`, the kernel `g_ε = (f * μ) d^{−ε}` lies in
`CriticalWiener` and its Bohr evaluation at `polePoint ε hε2.le` (`s = 1 − ε`) is the nonvanishing
Euler product `∑' n, (f * μ)(n)/n = ∏_p (1 − p^{−1}) L_p ≠ 0`. By the stabilizer–annihilator
dichotomy (`paidIdeal_conv_dichotomy_of_eq_ker`), for every `0 < ε < 1/2`:
1. `paidIdeal (f d^{−ε}) = paidIdeal (d^{−ε}) = RingHom.ker (bohrCharacter (1/2) (polePoint ε hε2.le))`;
2. `obstructionHull (f d^{−ε}) = obstructionHull (d^{−ε}) = {ω | ∀ p, p.Prime → ω.ω p = (polePoint ε hε2.le).ω p}`;
3. `Module.finrank ℂ (𝒲_{1/2} ⧸ paidIdeal (f d^{−ε})) = 1`. -/
theorem multiplicative_one_paidIdeal_obstructionHull_and_index_of_poleLocalFactor_ne_zero
    {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative) (hfp : ∀ p : ℕ, p.Prime → f p = 1)
    {B : ℝ} (hB : ∀ n, |f n| ≤ B) (hL : ∀ p : ℕ, p.Prime → poleLocalFactor f p ≠ 0)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ¬ ReceiverBounded (dampedSignWeight ⇑f ε) ∧
    paidIdeal (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le_const hB hε) =
      RingHom.ker (WienerAlgebraAt.bohrCharacter (1 / 2) (polePoint ε hε2.le)) ∧
    obstructionHull (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le_const hB hε) =
      {ω : BohrPoint | ∀ p : ℕ, p.Prime → ω.ω p = (polePoint ε hε2.le).ω p} ∧
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
      paidIdeal (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le_const hB hε)) = 1 := by
  let μR : ArithmeticFunction ℝ := (ArithmeticFunction.moebius : ArithmeticFunction ℤ)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 1)
  set g := f * μR
  have hg : g.IsMultiplicative := hf.mul ArithmeticFunction.isMultiplicative_moebius.intCast
  have hgp : ∀ p : ℕ, p.Prime → g p = 0 := fun p hp => by
    have := mul_moebius_apply_prime_pow f hp 0
    rwa [zero_add, pow_one, pow_zero, hf.map_one, hfp p hp, sub_self] at this
  have hW : CriticalWiener (dampedSignWeight ⇑g ε) :=
    criticalWiener_of_multiplicative hg hgp (B := 2 * B + 1) (by linarith)
      (fun p hp k hk => (abs_mul_moebius_apply_le hf hB hp k).trans
        (le_mul_of_one_le_right (by linarith) (by exact_mod_cast (by omega : 1 ≤ k)))) hε
  have hfg : f = g * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) := by
    simp only [g, μR]
    rw [mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]
  have hfun : dampedSignWeight ⇑f ε =
      RHTower.dirichletConv (dampedSignWeight ⇑g ε) (dampedSignWeight unitSign ε) := by
    funext n
    rw [← dampedSignWeight_zeta hε.ne', ← dampedSignWeight_dirichletConv]
    conv_lhs => rw [hfg]
    simp only [dampedSignWeight, mul_apply_eq_dirichletConv]
  have hker_unit : paidIdeal (dampedSignWeight unitSign ε) (summable_abs_smoothPower_div hε) =
      RingHom.ker (WienerAlgebraAt.bohrCharacter (1 / 2) (polePoint ε hε2.le)) := by
    ext k
    rw [mem_paidIdeal_smoothPower_iff hε hε2, RingHom.mem_ker, bohrCharacter_apply]
  have hdich_both := paidIdeal_conv_dichotomy_of_eq_ker (summable_abs_smoothPower_div hε)
    hker_unit hW
  have hunpaid_f : ¬ ReceiverBounded (dampedSignWeight ⇑f ε) :=
    not_receiverBounded_of_primes_one_of_poleLocalFactor_ne_zero hf hfp hB hε hε2.le hL
  have hnz : bohrEval (1 / 2) (realFn (dampedSignWeight ⇑g ε)) (polePoint ε hε2.le) ≠ 0 :=
    fun hz => hunpaid_f (hfun ▸ (hdich_both.1 hz).1)
  have hdich := hdich_both.2 hnz
  have hsf := summable_abs_dampedSign_div_of_abs_le_const hB hε
  have hid : paidIdeal (dampedSignWeight ⇑f ε) hsf =
      paidIdeal (dampedSignWeight unitSign ε) (summable_abs_smoothPower_div hε) := by
    rw [paidIdeal_congr_ne_zero (fun n _ => congrFun hfun n) hsf
      (summable_abs_dirichletConv_div hW (summable_abs_smoothPower_div hε))]
    exact hdich.2.1
  have hhull : obstructionHull (dampedSignWeight ⇑f ε) hsf =
      {ω : BohrPoint | ∀ p : ℕ, p.Prime → ω.ω p = (polePoint ε hε2.le).ω p} := by
    ext ω
    change (∀ k ∈ paidIdeal (dampedSignWeight ⇑f ε) hsf, bohrEval (1 / 2) k.toFn ω = 0) ↔ _
    rw [hid]
    exact mem_obstructionHull_smoothPower_iff hε hε2 ω
  have hfin : Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸ paidIdeal (dampedSignWeight ⇑f ε) hsf) = 1 := by
    rw [hid, hker_unit]
    exact finrank_quotient_ker_bohrCharacter (polePoint ε hε2.le)
  exact ⟨hunpaid_f, hid.trans hker_unit, hhull, hfin⟩

/-- **3B. Every bounded-by-`1` multiplicative weight pretending to `1` (`f(p) = 1`, `|f| ≤ 1`) has
the exact pole repairing ideal and codimension `1` across `0 < ε < 1/2`, regardless of its signs
on higher prime powers.** -/
theorem multiplicative_one_paidIdeal_obstructionHull_and_index_of_abs_le_one
    {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative) (hfp : ∀ p : ℕ, p.Prime → f p = 1)
    (hB : ∀ n, |f n| ≤ 1) {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ¬ ReceiverBounded (dampedSignWeight ⇑f ε) ∧
    paidIdeal (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le_const hB hε) =
      RingHom.ker (WienerAlgebraAt.bohrCharacter (1 / 2) (polePoint ε hε2.le)) ∧
    obstructionHull (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le_const hB hε) =
      {ω : BohrPoint | ∀ p : ℕ, p.Prime → ω.ω p = (polePoint ε hε2.le).ω p} ∧
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
      paidIdeal (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le_const hB hε)) = 1 :=
  multiplicative_one_paidIdeal_obstructionHull_and_index_of_poleLocalFactor_ne_zero hf hfp hB
    (fun _ hp => (lt_of_lt_of_le one_pos (one_le_poleLocalFactor hf hfp hB hp)).ne') hε hε2

/-- **3C. Exact Index Dichotomy for `1`-Pretentious Multiplicative Weights with Finite Local
Factors (`multiplicative_one_finiteLocalFactor_index_dichotomy`):**
If `f` is multiplicative with `f(p) = 1` at all primes, `|f| ≤ B`, and finite local factors
(`f(p^k) = 0` for `k > K`), then for every `0 < ε < 1/2`:
- if `∃ p, p.Prime ∧ poleLocalFactor f p = 0`, then `f d^{−ε}` is paid with `paidIdeal = ⊤`,
  `obstructionHull = ∅`, and `Module.finrank ℂ (𝒲_{1/2} ⧸ paidIdeal (f d^{−ε})) = 0`;
- if `∀ p, p.Prime → poleLocalFactor f p ≠ 0`, then `f d^{−ε}` is unpaid with
  `paidIdeal = RingHom.ker (bohrCharacter (1/2) (polePoint ε hε2.le))`,
  `obstructionHull = {ω | ∀ p, p.Prime → ω.ω p = (polePoint ε hε2.le).ω p}`, and
  `Module.finrank ℂ (𝒲_{1/2} ⧸ paidIdeal (f d^{−ε})) = 1`. -/
theorem multiplicative_one_finiteLocalFactor_index_dichotomy {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hfp : ∀ p : ℕ, p.Prime → f p = 1) {B : ℝ} (hB : ∀ n, |f n| ≤ B)
    {K : ℕ} (hfin : ∀ p : ℕ, p.Prime → ∀ k, K < k → f (p ^ k) = 0)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ((∃ p : ℕ, p.Prime ∧ poleLocalFactor f p = 0) →
      ReceiverBounded (dampedSignWeight ⇑f ε) ∧
      paidIdeal (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le_const hB hε) = ⊤ ∧
      obstructionHull (dampedSignWeight ⇑f ε)
        (summable_abs_dampedSign_div_of_abs_le_const hB hε) = ∅ ∧
      Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (dampedSignWeight ⇑f ε)
          (summable_abs_dampedSign_div_of_abs_le_const hB hε)) = 0) ∧
    ((∀ p : ℕ, p.Prime → poleLocalFactor f p ≠ 0) →
      ¬ ReceiverBounded (dampedSignWeight ⇑f ε) ∧
      paidIdeal (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le_const hB hε) =
        RingHom.ker (WienerAlgebraAt.bohrCharacter (1 / 2) (polePoint ε hε2.le)) ∧
      obstructionHull (dampedSignWeight ⇑f ε)
        (summable_abs_dampedSign_div_of_abs_le_const hB hε) =
        {ω : BohrPoint | ∀ p : ℕ, p.Prime → ω.ω p = (polePoint ε hε2.le).ω p} ∧
      Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (dampedSignWeight ⇑f ε)
          (summable_abs_dampedSign_div_of_abs_le_const hB hε)) = 1) := by
  have hsf := summable_abs_dampedSign_div_of_abs_le_const hB hε
  refine ⟨fun hex => ?_, fun hall =>
    multiplicative_one_paidIdeal_obstructionHull_and_index_of_poleLocalFactor_ne_zero
      hf hfp hB hall hε hε2⟩
  have hpaid : ReceiverBounded (dampedSignWeight ⇑f ε) :=
    (receiverBounded_iff_exists_poleLocalFactor_eq_zero hf hfp hB hfin hε hε2.le).2 hex
  exact ⟨hpaid, (paidIdeal_eq_top_iff_receiverBounded hsf).2 hpaid,
    (obstructionHull_eq_empty_iff_receiverBounded hsf).2 hpaid,
    finrank_quotient_paidIdeal_eq_zero_of_receiverBounded hsf hpaid⟩

/-- **Master Synthesis for Open Problem 9 (`actualReceiver_indexFormula_synthesis`):**
Packages the complete resolution of Open Problem 9:
1. Reverse inclusion, untied-obstruction exclusion, and zero-codimension index formula for the
   actual Möbius receiver `μ d^{−ε}` right of the zero width `zetaZeroAbscissa − 1/2 < ε < 1/2`;
2. Exact `WienerUnitOrbit` equivalence and identical `paidIdeal`, `obstructionHull`, `rank`, and
   `finrank` between the Liouville receiver `λ d^{−ε}` and the Möbius receiver `μ d^{−ε}`;
3. Unconditional zero-codimension index formula (`paidIdeal = ⊤`, `obstructionHull = ∅`,
   `finrank = 0`) for character-pretentious multiplicative weights `f(p) = χ(p)` (`χ ≠ 1`, `|f| ≤ 1`)
   at all `ε > 0`;
4. Exact codimension-`1` pole index formula (`paidIdeal = ker(polePoint ε)`,
   `obstructionHull = {polePoint ε}`, `finrank = 1`) for `1`-pretentious multiplicative weights
   `f(p) = 1` with nonvanishing local factors (`poleLocalFactor f p ≠ 0`, including all `|f| ≤ 1`)
   and codimension-`0`/`1` dichotomy for finite local factors. -/
theorem actualReceiver_indexFormula_synthesis :
    (∀ {ε : ℝ} (hεΘ : zetaZeroAbscissa - 1 / 2 < ε) (_hε2 : ε < 1 / 2),
      have hε : 0 < ε := by linarith [half_le_zetaZeroAbscissa]
      obstructionHull (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) =
        translatedOffLineZeroHull ε ∧
      translatedOffLineZeroHull ε = ∅ ∧
      Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε)) = 0) ∧
    (∀ {ε : ℝ} (hε : 0 < ε),
      WienerUnitOrbit (pmPowerDampedRealWeight ε) (dampedSignWeight RHTower.liouvilleR ε) ∧
      paidIdeal (dampedSignWeight RHTower.liouvilleR ε) (summable_abs_dampedLiouville_div hε) =
        paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) ∧
      obstructionHull (dampedSignWeight RHTower.liouvilleR ε) (summable_abs_dampedLiouville_div hε) =
        obstructionHull (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε)) ∧
    (∀ {q : ℕ} [NeZero q] {χ : MulChar (ZMod q) ℤ} (_hχ : χ ≠ 1)
      {f : ArithmeticFunction ℝ} (_hf : f.IsMultiplicative) (hbd : ∀ n, |f n| ≤ 1)
      (_hfp : ∀ p : ℕ, p.Prime → f p = charSign χ p) {ε : ℝ} (hε : 0 < ε),
        paidIdeal (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le hbd hε) = ⊤ ∧
        obstructionHull (dampedSignWeight ⇑f ε)
          (summable_abs_dampedSign_div_of_abs_le hbd hε) = ∅ ∧
        Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
          paidIdeal (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le hbd hε)) = 0) ∧
    (∀ {f : ArithmeticFunction ℝ} (_hf : f.IsMultiplicative)
      (_hfp : ∀ p : ℕ, p.Prime → f p = 1) (hB : ∀ n, |f n| ≤ 1) {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2),
        paidIdeal (dampedSignWeight ⇑f ε) (summable_abs_dampedSign_div_of_abs_le_const hB hε) =
          RingHom.ker (WienerAlgebraAt.bohrCharacter (1 / 2) (polePoint ε hε2.le)) ∧
        Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
          paidIdeal (dampedSignWeight ⇑f ε)
            (summable_abs_dampedSign_div_of_abs_le_const hB hε)) = 1) := by
  refine ⟨fun hεΘ hε2 => ?_, fun hε => ?_, ?_, ?_⟩
  · exact ⟨(moebius_reverse_inclusion_and_index_above_zeroWidth hεΘ hε2).2.2.1,
           (moebius_reverse_inclusion_and_index_above_zeroWidth hεΘ hε2).2.2.2.1,
           (moebius_reverse_inclusion_and_index_above_zeroWidth hεΘ hε2).2.2.2.2.2.2⟩
  · exact ⟨wienerUnitOrbit_moebius_liouville hε,
           (liouville_paidIdeal_obstructionHull_and_index_eq_moebius hε).1,
           (liouville_paidIdeal_obstructionHull_and_index_eq_moebius hε).2.1⟩
  · intro q _ χ hχ f hf hbd hfp ε hε
    exact ⟨(multiplicative_char_paidIdeal_obstructionHull_and_index hχ hf hbd hfp hε).2.1,
           (multiplicative_char_paidIdeal_obstructionHull_and_index hχ hf hbd hfp hε).2.2.1,
           (multiplicative_char_paidIdeal_obstructionHull_and_index hχ hf hbd hfp hε).2.2.2.2⟩
  · intro f hf hfp hB ε hε hε2
    exact ⟨(multiplicative_one_paidIdeal_obstructionHull_and_index_of_abs_le_one hf hfp hB hε hε2).2.1,
           (multiplicative_one_paidIdeal_obstructionHull_and_index_of_abs_le_one hf hfp hB hε hε2).2.2.2⟩

end

end GaloisForLFunctions.ArithmeticOrientationTheory
