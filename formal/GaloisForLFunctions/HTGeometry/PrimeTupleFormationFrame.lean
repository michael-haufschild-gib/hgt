import GaloisForLFunctions.HTGeometry.PermutohedralScheduleConservation
import GaloisForLFunctions.HTGeometry.DiagonalHistoryResponse

/-!
# Uniform all-prime formation frames at every fixed grade

An unordered `r`-tuple of distinct primes `I = {p_1 < ⋯ < p_r}` carries the grades
`λ_i = log p_i` and the endpoint `e_{p_1 ⋯ p_r}`; unique factorization makes distinct tuples have
distinct endpoints.  Every nonempty subset rate of prime logarithms is at least `λ₀ = log 2`, so
comparing exponential phases gives the Erlang lower envelope `G_{2^r - 1, log 2} ≤ H_I ≤ 1`
`(PGE.19)`, `(GFH.26)`, `(AFD.14)`.  The formed response `d ↦ Σ_I d_I H_I(t) e_I` is therefore a
frame: `c_{r,T}² ‖d‖² ≤ ‖𝒢_{r,T} d‖² ≤ T ‖d‖²` with `c_{r,T}² = ∫₀ᵀ G_{2^r-1}²`
`(PGE.22)`, `(GFH.29)`, `(AFD.17)`; it is injective with closed range and inverse norm at most
`c_{r,T}⁻¹` on its range.
-/

open scoped InnerProductSpace
open MeasureTheory Set Filter Topology HTGeometry RHTower

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

open Permutohedral

/-! ### The Erlang envelope of the subset-phase law -/

theorem forall₂_replicate_le {l : ℝ} :
    ∀ {L : List ℝ}, (∀ x ∈ L, l ≤ x) → List.Forall₂ (· ≤ ·) (List.replicate L.length l) L
  | [], _ => List.Forall₂.nil
  | x :: _, h => List.Forall₂.cons (h x List.mem_cons_self)
      (forall₂_replicate_le fun y hy => h y (List.mem_cons_of_mem x hy))

theorem le_of_mem_subsetRates {r : ℕ} {lam : Fin r → ℝ} {l : ℝ} (hlam : ∀ i, 0 < lam i)
    (hl : ∀ i, l ≤ lam i) : ∀ x ∈ subsetRates lam, l ≤ x := fun x hx => by
  obtain ⟨S, hS, rfl⟩ := List.mem_map.1 hx
  rw [Finset.mem_toList] at hS
  obtain ⟨i, hi⟩ := (Finset.mem_filter.1 hS).2
  exact (hl i).trans (Finset.single_le_sum (fun j _ => (hlam j).le) hi)

/-- **Erlang lower envelope**: if every grade is at least `l > 0`, then
`G_{2^r - 1, l} ≤ H_r` on `[0, ∞)`. -/
theorem erlangCDF_le_subsetCDF {r : ℕ} {lam : Fin r → ℝ} {l : ℝ} (hl0 : 0 < l)
    (hlam : ∀ i, 0 < lam i) (hl : ∀ i, l ≤ lam i) {t : ℝ} (ht : 0 ≤ t) :
    erlangCDF (2 ^ r - 1) l t ≤ subsetCDF lam t := by
  have h := hypoCDFList_mono (forall₂_replicate_le (le_of_mem_subsetRates hlam hl))
    (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact hl0) ht
  rwa [length_subsetRates, hypoCDFList_replicate] at h

/-- The Erlang floor `c_{N,T}² = ∫₀ᵀ G_{N, log 2}(t)² dt`. -/
def erlangFloor (N : ℕ) (T : ℝ) : ℝ := ∫ t in (0 : ℝ)..T, erlangCDF N (Real.log 2) t ^ 2

theorem erlangFloor_pos (N : ℕ) {T : ℝ} (hT : 0 < T) : 0 < erlangFloor N T := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (Continuous.intervalIntegrable (by unfold erlangCDF; fun_prop) _ _)
    (fun t ht => pow_pos (erlangCDF_pos N hl ht.1) 2) hT

/-! ### Prime tuples -/

/-- Unordered `r`-tuples of distinct primes. -/
abbrev PrimeTuple (r : ℕ) : Type := {s : Finset ℕ // s.card = r ∧ ∀ p ∈ s, p.Prime}

namespace PrimeTuple

variable {r : ℕ}

/-- The arithmetic endpoint `p_1 ⋯ p_r ∈ ℕ≥1`. -/
def endpoint (I : PrimeTuple r) : ℕ+ :=
  ⟨∏ p ∈ I.1, p, Finset.prod_pos fun p hp => (I.2.2 p hp).pos⟩

/-- Unique factorization: distinct prime tuples have distinct endpoints. -/
theorem endpoint_injective : Function.Injective (endpoint (r := r)) := by
  intro I J h
  have h1 : (∏ p ∈ I.1, p) = ∏ p ∈ J.1, p := congrArg PNat.val h
  apply Subtype.ext
  rw [← Nat.primeFactors_prod I.2.2, ← Nat.primeFactors_prod J.2.2, h1]

/-- The increasing enumeration `p_1 < ⋯ < p_r`. -/
def prime (I : PrimeTuple r) (i : Fin r) : ℕ := I.1.orderEmbOfFin I.2.1 i

theorem prime_prime (I : PrimeTuple r) (i : Fin r) : (I.prime i).Prime :=
  I.2.2 _ (Finset.orderEmbOfFin_mem _ _ _)

theorem prime_strictMono (I : PrimeTuple r) : StrictMono I.prime :=
  (I.1.orderEmbOfFin I.2.1).strictMono

/-- The grades `λ_i = log p_i`. -/
def grades (I : PrimeTuple r) (i : Fin r) : ℝ := Real.log (I.prime i)

theorem log_two_le_grades (I : PrimeTuple r) (i : Fin r) : Real.log 2 ≤ I.grades i :=
  Real.log_le_log two_pos (by exact_mod_cast (I.prime_prime i).two_le)

theorem grades_pos (I : PrimeTuple r) (i : Fin r) : 0 < I.grades i :=
  (Real.log_pos one_lt_two).trans_le (I.log_two_le_grades i)

theorem grades_strictMono (I : PrimeTuple r) : StrictMono I.grades := fun i j hij =>
  Real.log_lt_log (by exact_mod_cast (I.prime_prime i).pos)
    (by exact_mod_cast I.prime_strictMono hij)

theorem grades_injective (I : PrimeTuple r) : Function.Injective I.grades :=
  I.grades_strictMono.injective

end PrimeTuple

/-! ### The formed response over prime tuples -/

/-- The formed histories `t ↦ H_I(t⁺) e_I` over prime `r`-tuples `(PGE.21)`, `(AFD.16)`. -/
def formationFamily (r : ℕ) : HistoryFamily (PrimeTuple r) where
  endpoint := PrimeTuple.endpoint
  endpoint_injective := PrimeTuple.endpoint_injective
  weight I t := subsetCDF I.grades (max t 0)
  continuous_weight I := (continuous_hypoCDFList _).comp (continuous_id.max continuous_const)
  abs_weight_le I t := by
    have h0 : 0 ≤ subsetCDF I.grades (max t 0) :=
      hypoCDFList_nonneg (subsetRates_pos I.grades_pos) (le_max_right t 0)
    have h1 : subsetCDF I.grades (max t 0) ≤ 1 :=
      hypoCDFList_le_one (subsetRates_pos I.grades_pos) (le_max_right t 0)
    rw [abs_le]
    exact ⟨by linarith, h1⟩

theorem formation_energy_eq {r : ℕ} {T : ℝ} (hT : 0 ≤ T) (I : PrimeTuple r) :
    (formationFamily r).energy T I = ∫ t in (0 : ℝ)..T, subsetCDF I.grades t ^ 2 := by
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hT] at ht
  show subsetCDF I.grades (max t 0) ^ 2 = _
  rw [max_eq_left ht.1]

theorem erlangFloor_le_energy {r : ℕ} {T : ℝ} (hT : 0 ≤ T) (I : PrimeTuple r) :
    erlangFloor (2 ^ r - 1) T ≤ (formationFamily r).energy T I := by
  rw [formation_energy_eq hT]
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine intervalIntegral.integral_mono_on hT
    (Continuous.intervalIntegrable (by unfold erlangCDF; fun_prop) _ _)
    (Continuous.intervalIntegrable ((continuous_hypoCDFList _).pow 2) _ _) fun t ht => ?_
  have h0 : 0 ≤ erlangCDF (2 ^ r - 1) (Real.log 2) t := by
    rw [← hypoCDFList_replicate]
    exact hypoCDFList_nonneg (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact hl) ht.1
  exact pow_le_pow_left₀ h0
    (erlangCDF_le_subsetCDF hl I.grades_pos I.log_two_le_grades ht.1) 2

/-- **The fixed-grade formation frame** `c_{r,T}² ‖d‖² ≤ ‖𝒢_{r,T} d‖² ≤ T ‖d‖²`
`(PGE.22)`, `(GFH.29)`, `(AFD.17)`. -/
theorem formation_frame {r : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (d : HistoryFamily.Controls (PrimeTuple r)) :
    erlangFloor (2 ^ r - 1) T * ‖d‖ ^ 2 ≤ ‖(formationFamily r).response T d‖ ^ 2 ∧
      ‖(formationFamily r).response T d‖ ^ 2 ≤ T * ‖d‖ ^ 2 :=
  (formationFamily r).frame_bounds hT (erlangFloor_le_energy hT)
    ((formationFamily r).energy_le hT) d

theorem formation_injective {r : ℕ} {T : ℝ} (hT : 0 < T) :
    Function.Injective ((formationFamily r).response T) :=
  (formationFamily r).response_injective hT.le (erlangFloor_pos _ hT) (erlangFloor_le_energy hT.le)

theorem isClosed_range_formation {r : ℕ} {T : ℝ} (hT : 0 < T) :
    IsClosed (Set.range ((formationFamily r).response T)) :=
  (formationFamily r).isClosed_range_response hT.le (erlangFloor_pos _ hT)
    (erlangFloor_le_energy hT.le)

/-- The inverse on the range has norm at most `c_{r,T}⁻¹`. -/
theorem norm_le_erlangFloor_inv_mul {r : ℕ} {T : ℝ} (hT : 0 < T)
    (d : HistoryFamily.Controls (PrimeTuple r)) :
    ‖d‖ ≤ (Real.sqrt (erlangFloor (2 ^ r - 1) T))⁻¹ * ‖(formationFamily r).response T d‖ :=
  (formationFamily r).norm_le_inv_mul_response hT.le (erlangFloor_pos _ hT)
    (erlangFloor_le_energy hT.le) d

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
