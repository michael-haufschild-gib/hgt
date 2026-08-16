import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Sparse forbidden deletion and the near-Hall double count

Two elementary laws carry the growing-breadth reservoir cube.

The first is a deletion law: a structured supply of size at least `L` from which the products
using one of `#F` forbidden primes are removed still has size at least `L/2`, as soon as the total
removed is at most `L/2`.  The two ratio estimates that verify that smallness are pure growth
comparisons — a power of `log y` against a power of `y`, and a power of `log log y` against a power
of `log y`.

The second is the near-Hall double count: if every anchor reaches at least `d` terminals and every
terminal is reached by at most `D` anchors, the terminal set has at least `#A·d/D` elements.
-/

open Filter Topology Asymptotics

namespace RHTower

/-! ## The deletion law -/

/-- **Sparse deletion.**  Removing the elements that use one of a sparse family of forbidden
classes leaves at least half the supply, provided the total removed is at most half. -/
theorem card_sdiff_biUnion_ge {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (F : Finset β) (T : β → Finset α) (L M : ℝ)
    (hL : L ≤ S.card) (hM : ∀ ℓ ∈ F, ((T ℓ).card : ℝ) ≤ M)
    (hsmall : (F.card : ℝ) * M ≤ L / 2) :
    L / 2 ≤ ((S \ F.biUnion T).card : ℝ) := by
  have hsplit : ((S \ F.biUnion T).card : ℝ) + ((S ∩ F.biUnion T).card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Finset.card_sdiff_add_card_inter S (F.biUnion T))
  have hinter : ((S ∩ F.biUnion T).card : ℝ) ≤ ((F.biUnion T).card : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hunion : ((F.biUnion T).card : ℝ) ≤ ∑ ℓ ∈ F, ((T ℓ).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  have hsum : ∑ ℓ ∈ F, ((T ℓ).card : ℝ) ≤ (F.card : ℝ) * M := by
    calc ∑ ℓ ∈ F, ((T ℓ).card : ℝ) ≤ ∑ _ℓ ∈ F, M := Finset.sum_le_sum hM
      _ = (F.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
  linarith

/-! ## The growth comparisons -/

/-- A power of the logarithm is negligible against any power of the variable. -/
theorem tendsto_log_rpow_div_rpow (r : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun y : ℝ => Real.log y ^ r / y ^ s) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop r hs).tendsto_div_nhds_zero

/-- A power of the iterated logarithm is negligible against any power of the logarithm. -/
theorem tendsto_logLog_rpow_div_log_rpow (r : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun y : ℝ => Real.log (Real.log y) ^ r / Real.log y ^ s) atTop (𝓝 0) :=
  (tendsto_log_rpow_div_rpow r hs).comp Real.tendsto_log_atTop

/-! ## The near-Hall double count -/

/-- **The near-Hall law.**  Counting anchor--terminal incidences from both sides: if every anchor
reaches at least `d` distinct terminals and every terminal is reached by at most `D` anchors, the
terminal set has at least `#A·d/D` elements. -/
theorem card_terminals_ge_of_rowDegree_codegree {A T : Type*} [DecidableEq T]
    (𝒜 : Finset A) (N : Finset T) (E : A → Finset T) (d D : ℝ) (hD : 0 < D)
    (hrow : ∀ n ∈ 𝒜, d ≤ ((E n).card : ℝ)) (hsub : ∀ n ∈ 𝒜, E n ⊆ N)
    (hcol : ∀ v ∈ N, (((𝒜.filter fun n => v ∈ E n)).card : ℝ) ≤ D) :
    (𝒜.card : ℝ) * d / D ≤ (N.card : ℝ) := by
  classical
  have hcount : ∑ n ∈ 𝒜, ((E n).card : ℝ)
      = ∑ v ∈ N, (((𝒜.filter fun n => v ∈ E n)).card : ℝ) := by
    have hnat : ∑ n ∈ 𝒜, (E n).card = ∑ v ∈ N, ((𝒜.filter fun n => v ∈ E n)).card := by
      have hleft : ∀ n ∈ 𝒜, (E n).card = ∑ v ∈ N, if v ∈ E n then 1 else 0 := by
        intro n hn
        rw [← Finset.card_filter (fun v => v ∈ E n) N]
        congr 1
        rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (hsub n hn)]
      have hright : ∀ v ∈ N, ((𝒜.filter fun n => v ∈ E n)).card
          = ∑ n ∈ 𝒜, if v ∈ E n then 1 else 0 := by
        intro v _
        rw [← Finset.card_filter (fun n => v ∈ E n) 𝒜]
      rw [Finset.sum_congr rfl hleft, Finset.sum_congr rfl hright, Finset.sum_comm]
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hnat
  have hlow : (𝒜.card : ℝ) * d ≤ ∑ n ∈ 𝒜, ((E n).card : ℝ) := by
    calc (𝒜.card : ℝ) * d = ∑ _n ∈ 𝒜, d := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ 𝒜, ((E n).card : ℝ) := Finset.sum_le_sum hrow
  have hhigh : ∑ v ∈ N, (((𝒜.filter fun n => v ∈ E n)).card : ℝ) ≤ (N.card : ℝ) * D := by
    calc ∑ v ∈ N, (((𝒜.filter fun n => v ∈ E n)).card : ℝ) ≤ ∑ _v ∈ N, D :=
          Finset.sum_le_sum hcol
      _ = (N.card : ℝ) * D := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [div_le_iff₀ hD]
  linarith [hcount ▸ hlow, hhigh]

/-! ## The fixed-divisor capacity no-go -/

/-- **The fixed-divisor load bound.**  If every cube sends its distinguished anchor to a terminal
in a set `T`, and every terminal carries load at most one, the total anchored load is at most
`#T`.  Applied to terminals all divisible by a fixed integer `P`, `#T` is the count of multiples
of `P` in the window, so a large fixed divisor leaves most of the anchor family uncovered. -/
theorem total_load_le_card_terminals {C V : Type*} [DecidableEq V]
    (cubes : Finset C) (w : C → ℝ) (τ : C → V) (T : Finset V)
    (hτ : ∀ c ∈ cubes, τ c ∈ T)
    (hload : ∀ v ∈ T, ∑ c ∈ cubes.filter fun c => τ c = v, w c ≤ 1) :
    ∑ c ∈ cubes, w c ≤ (T.card : ℝ) := by
  classical
  have hfiber : ∑ c ∈ cubes, w c = ∑ v ∈ T, ∑ c ∈ cubes.filter fun c => τ c = v, w c :=
    (Finset.sum_fiberwise_of_maps_to hτ w).symm
  rw [hfiber]
  calc ∑ v ∈ T, ∑ c ∈ cubes.filter fun c => τ c = v, w c ≤ ∑ _v ∈ T, (1 : ℝ) :=
        Finset.sum_le_sum hload
    _ = (T.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The uncovered anchor load.**  Subtracting the anchored load from the unit capacity of the
anchor family. -/
theorem uncovered_load_ge {C V A : Type*} [DecidableEq V]
    (cubes : Finset C) (w : C → ℝ) (τ : C → V) (T : Finset V) (𝒜 : Finset A)
    (hτ : ∀ c ∈ cubes, τ c ∈ T)
    (hload : ∀ v ∈ T, ∑ c ∈ cubes.filter fun c => τ c = v, w c ≤ 1) :
    (𝒜.card : ℝ) - (T.card : ℝ) ≤ (𝒜.card : ℝ) - ∑ c ∈ cubes, w c := by
  have := total_load_le_card_terminals cubes w τ T hτ hload
  linarith

end RHTower
