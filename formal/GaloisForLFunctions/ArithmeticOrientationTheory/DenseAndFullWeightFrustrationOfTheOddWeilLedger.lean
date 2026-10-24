import GaloisForLFunctions.ArithmeticOrientationTheory.TheFrustrationIndexCountsPrimeSums
import GaloisForLFunctions.ArithmeticOrientationTheory.TheLatticeOddLedgerIsBalanced
import GaloisForLFunctions.ArithmeticOrientationTheory.FrustrationBoundsTheGroundEnergyFromBelow
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.ArithmeticCanonicalPathCalibration
import GaloisForLFunctions.SquareRootThreshold.TheContactApertureOfTheGroundEnergyPath

/-!
# Dense and full-weight frustration of the odd Weil ledger

This module resolves Open Problem 1 of Arithmetic Orientation Theory: the frustration index and
frustration mass of the odd Weil ledger off the lattice on dense position sets in `(0, A]`, at the
source-faithful full archimedean–polar weight `α = 1, β = 1` (`weilLedgerKernel 1 1`), and their
relation to the trial-profile upper bound `4 ν_w / n`, canonical-path payment, and the restricted
Weil ground energy `μ(A)` across the contact aperture `A* ≥ 3/10`.

1. **Sub-sample monotonicity, disjoint fiber packing, and dense cut reduction.**
   * Restricting any switching along an injective map `e : ι₀ → ι` drops only nonnegative
     misalignment terms (`misalignedCost_comp_injective_le`), so both the frustration index and the
     frustration mass are monotone under sub-sampling (`frustrationIndex_comp_injective_le`,
     `frustrationMass_comp_injective_le`). Adding arbitrarily dense points in `(0, A]` never allows
     switching to reduce the frustration index or mass below that of an embedded sub-sample.
   * Across pairwise disjoint fibers `κ × ι₀ → ι`, the frustration index and frustration mass are
     superadditive (`sum_frustrationIndex_fiber_le`, `sum_frustrationMass_fiber_le`).
   * At any sign vector `s`, the incidence energy is the degree deficit plus twice the misaligned
     mass (`incidenceEnergy_signVector_eq`): `4 ν_w / n` is the trial-profile upper bound on the
     Dirichlet ground energy, whereas a lower bound on the incidence energy requires the frustrated
     mass to be paid.

2. **The polar hyperbolic barrier and midpoint quenching at full archimedean weight.**
   * The polar part `-4 cosh(u/2)` of `weilKernel` obeys the exact hyperbolic identity
     `cosh((x + y)/2) - cosh((x - y)/2) = 2 sinh(x/2) sinh(y/2)` (`cosh_half_add_sub_cosh_half_sub`),
     giving the universal barrier
     `weilKernel |x + y| - weilKernel |x - y| < -8 sinh(x/2) sinh(y/2)` for all `x ≠ y > 0`
     (`weilKernel_add_sub_weilKernel_sub_lt_neg_eight_sinh`).
   * Consequently, on the midpoint-matched family `matchedPos Q` (`½ log(3q/2), ½ log(2q/3)` for
     primes `q ≥ 5`) of `TheFrustrationIndexCountsPrimeSums` — which had frustration index `2|Q|` as
     `α → 0` — the full weight `α = 1, β = 1` quenches every partner overlap to `< 0`
     (`oddFold_matchedPos_weilLedgerKernel_one_neg`). At full weight `matchedPos Q` is balanced with
     `frustrationIndex = 0` and `frustrationMass = 0` (`frustrationIndex_matchedPos_weilLedgerKernel_one_eq_zero`,
     `frustrationMass_matchedPos_weilLedgerKernel_one_eq_zero`).

3. **Exact frustration index and mass at full weight `α = 1, β = 1` on `primeTrianglePos`,
   `packedPrimePos`, and dense multi-triangle packings.**
   * On `primeTrianglePos` (`Fin 3`) at `α = 1, β = 1`, the frustration index is unconditionally `2`
     for every budget `b` (`frustrationIndex_primeTriangle_weilLedgerKernel_one`), and the
     frustration mass lies in `(2/7, 4/5)` (`frustrationMass_primeTriangle_weilLedgerKernel_one_bounds`).
   * On `packedPrimePos` (`Fin 4`) at `α = 1, β = 1`, where two anti-aligned prime sums `(1, 2)` and
     `(1, 3)` share vertex `1` (violating the sparsity condition `4D ≤ n`), the unswitched misaligned
     count is `4`, and switching vertex `1` (`s = ![1, -1, 1, 1]`) trades both prime-sum edges for
     the single aligned hub edge `(0, 1)`, reducing the frustration index to `2`
     (`frustrationIndex_packedPrime_weilLedgerKernel_one`) and the frustration mass below `4/5`
     (`frustrationMass_packedPrime_weilLedgerKernel_one_lt`).
   * By continuity of `oddFold` at `primeTrianglePos` and disjoint fiber superadditivity, for every
     multiplicity `M ≥ 1` there are `3M`-point samples in `(0, log 5]` at full weight `α = 1, β = 1`
     with `frustrationIndex ≥ 2M` and `frustrationMass ≥ (2/7) M`
     (`exists_dense_primeTriangle_packing_weilLedgerKernel_one`).

4. **Collar-skimming survival at full weight `α = 1, β = 1`.**
   * For any finite family `I` of primes `π : I → ℕ` (`2 ≤ card I`), placing lower points at
     `δ i → 0⁺` and upper points at `log(π i) - δ i` (`collarPos`) isolates all prime sums to the
     partner pairs via the elementary gap `log(N + 1) - log N ≥ 1/(N + 1)` (`exp_log_nat_add_ne_nat`,
     `eq_collarPartner_of_exp_eq`).
   * As `δ i → 0⁺`, `weilKernel (log q) - weilKernel (log q - 2δ i) → 0`, so at **every** fixed
     `α > 0, β > 0` (in particular `α = 1, β = 1`), the frustration index of `collarPos` is
     `2 · card I` (`frustrationIndex_collarPos_fullWeight`). Instantiated on `↥Q × Fin M`, dense
     collar-skimming samples of size `2 M |Q|` in `(0, max_{q ∈ Q} log q]` reach full frustration
     index `2 M |Q|` at `α = 1, β = 1` (`exists_collarPos_frustrationIndex_eq_two_mul`).

5. **The sub-prime contact regime `A ≤ 3/10` and synthesis with `μ(A)` and `zetaContactAperture`.**
   * For any sample in `(0, A]` with `A < ½ log 2` (including the certified contact window
     `A ≤ 3/10`), `primeSumPairs p = ∅`, `frustrationIndex = 0`, `frustrationMass = 0`, and the odd
     Weil ledger is balanced (`frustrationIndex_eq_zero_of_le_threeTenths`), while `μ(A) ≥ 1/5000`
     and `3/10 ≤ zetaContactAperture` off RH (`oddWeilLedger_offLattice_frustration_and_contact_synthesis`).
-/

open Finset ArithmeticFunction Filter Topology
open scoped Matrix

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open _root_.Zeta23 _root_.RHTower
open SignedArithmeticEnergyIncidence
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.SquareRootThreshold

noncomputable section
set_option autoImplicit false

/-! ### 1. Sub-sample monotonicity, disjoint fiber packing, and trial-profile energy -/

section Subsample

variable {ι₀ ι : Type*} [Fintype ι₀] [DecidableEq ι₀] [Fintype ι] [DecidableEq ι]

/-- Restricting a sign vector along an injective embedding `e : ι₀ → ι` drops only nonnegative
misalignment terms. -/
theorem misalignedCost_comp_injective_le {e : ι₀ → ι} (he : Function.Injective e)
    (s : ι → ℝ) {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t) (c : ι → ι → ℝ) :
    misalignedCost (fun i => s (e i)) g (fun i j => c (e i) (e j)) ≤ misalignedCost s g c := by
  unfold misalignedCost
  have h1 : ∀ i : ι₀,
      ∑ j : ι₀, (if i ≠ j ∧ 0 < s (e i) * s (e j) * c (e i) (e j) then g (c (e i) (e j)) else 0) =
      ∑ j ∈ univ.map ⟨e, he⟩, (if e i ≠ j ∧ 0 < s (e i) * s j * c (e i) j then g (c (e i) j) else 0) := by
    intro i
    rw [sum_map]
    refine sum_congr rfl fun j _ => ?_
    simp [he.ne_iff]
  simp_rw [h1]
  have h2 : ∑ i : ι₀, ∑ j ∈ univ.map ⟨e, he⟩,
      (if e i ≠ j ∧ 0 < s (e i) * s j * c (e i) j then g (c (e i) j) else 0) =
      ∑ i ∈ univ.map ⟨e, he⟩, ∑ j ∈ univ.map ⟨e, he⟩,
        (if i ≠ j ∧ 0 < s i * s j * c i j then g (c i j) else 0) := by
    rw [sum_map]
    rfl
  rw [h2]
  have hnn : ∀ i j : ι, 0 ≤ (if i ≠ j ∧ 0 < s i * s j * c i j then g (c i j) else 0) := fun i j => by
    split_ifs <;> [exact hg _; exact le_rfl]
  refine (sum_le_sum fun i _ => sum_le_univ_sum_of_nonneg (hnn i)).trans ?_
  exact sum_le_univ_sum_of_nonneg fun i => sum_nonneg fun j _ => hnn i j

theorem misalignedCount_comp_injective_le {e : ι₀ → ι} (he : Function.Injective e)
    (s : ι → ℝ) (c : ι → ι → ℝ) :
    misalignedCount (fun i => s (e i)) (fun i j => c (e i) (e j)) ≤ misalignedCount s c := by
  have := misalignedCost_comp_injective_le he s (g := fun _ => 1) (fun _ => by norm_num) c
  rw [← misalignedCount_eq_cost, ← misalignedCount_eq_cost] at this
  exact_mod_cast this

theorem misalignedMass_comp_injective_le {e : ι₀ → ι} (he : Function.Injective e)
    (s : ι → ℝ) (c : ι → ι → ℝ) :
    misalignedMass (fun i => s (e i)) (fun i j => c (e i) (e j)) ≤ misalignedMass s c :=
  misalignedCost_comp_injective_le he s abs_nonneg c

/-- **Sub-sample monotonicity of the frustration index**: embedding `ι₀` injectively into a larger
(or denser) sample `ι` never decreases the frustration index. -/
theorem frustrationIndex_comp_injective_le {e : ι₀ → ι} (he : Function.Injective e)
    (c : ι → ι → ℝ) :
    frustrationIndex (fun i j => c (e i) (e j)) ≤ frustrationIndex c := by
  obtain ⟨s, hs, hseq⟩ := frustrationIndex_mem c
  rw [← hseq]
  have hse : IsSignVector (fun i => s (e i)) := fun i => hs (e i)
  exact (frustrationIndex_le hse _).trans (misalignedCount_comp_injective_le he s c)

/-- **Sub-sample monotonicity of the frustration mass**: embedding `ι₀` injectively into a larger
(or denser) sample `ι` never decreases the frustration mass. -/
theorem frustrationMass_comp_injective_le {e : ι₀ → ι} (he : Function.Injective e)
    (c : ι → ι → ℝ) :
    frustrationMass (fun i j => c (e i) (e j)) ≤ frustrationMass c := by
  refine le_ciInf fun ⟨s, hs⟩ => ?_
  have hse : IsSignVector (fun i => s (e i)) := fun i => hs (e i)
  exact (frustrationMass_le hse _).trans (misalignedMass_comp_injective_le he s c)

/-- **Disjoint fiber superadditivity of misaligned cost**: across pairwise disjoint fibers
`e : κ × ι₀ → ι`, the misaligned cost is at least the sum of the fiber misaligned costs. -/
theorem sum_misalignedCost_fiber_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    {e : κ × ι₀ → ι} (he : Function.Injective e) (s : ι → ℝ) {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t)
    (c : ι → ι → ℝ) :
    ∑ r : κ, misalignedCost (fun i => s (e (r, i))) g (fun i j => c (e (r, i)) (e (r, j))) ≤
      misalignedCost s g c := by
  refine le_trans ?_ (misalignedCost_comp_injective_le he s hg c)
  unfold misalignedCost
  rw [Fintype.sum_prod_type]
  refine sum_le_sum fun r _ => sum_le_sum fun i _ => ?_
  rw [Fintype.sum_prod_type]
  have hnn : ∀ r' : κ, 0 ≤ ∑ j : ι₀,
      (if (r, i) ≠ (r', j) ∧ 0 < s (e (r, i)) * s (e (r', j)) * c (e (r, i)) (e (r', j)) then
        g (c (e (r, i)) (e (r', j))) else 0) :=
    fun r' => sum_nonneg fun j _ => by split_ifs <;> [exact hg _; exact le_rfl]
  refine le_trans (le_of_eq ?_) (single_le_sum (fun r' _ => hnn r') (mem_univ r))
  refine sum_congr rfl fun j _ => ?_
  simp [Prod.mk.injEq]

/-- **Disjoint fiber superadditivity of the frustration index** on dense samples. -/
theorem sum_frustrationIndex_fiber_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    {e : κ × ι₀ → ι} (he : Function.Injective e) (c : ι → ι → ℝ) :
    ∑ r : κ, frustrationIndex (fun i j => c (e (r, i)) (e (r, j))) ≤ frustrationIndex c := by
  obtain ⟨s, hs, hseq⟩ := frustrationIndex_mem c
  rw [← hseq]
  have h1 : ∀ r : κ, frustrationIndex (fun i j => c (e (r, i)) (e (r, j))) ≤
      misalignedCount (fun i => s (e (r, i))) (fun i j => c (e (r, i)) (e (r, j))) :=
    fun r => frustrationIndex_le (fun i => hs (e (r, i))) _
  refine (sum_le_sum fun r _ => h1 r).trans ?_
  have h2 := sum_misalignedCost_fiber_le he s (g := fun _ => 1) (fun _ => by norm_num) c
  simp_rw [← misalignedCount_eq_cost] at h2
  exact_mod_cast h2

/-- **Disjoint fiber superadditivity of the frustration mass** on dense samples. -/
theorem sum_frustrationMass_fiber_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    {e : κ × ι₀ → ι} (he : Function.Injective e) (c : ι → ι → ℝ) :
    ∑ r : κ, frustrationMass (fun i j => c (e (r, i)) (e (r, j))) ≤ frustrationMass c := by
  refine le_ciInf fun ⟨s, hs⟩ => ?_
  refine (sum_le_sum fun r _ => frustrationMass_le (fun i => hs (e (r, i))) _).trans ?_
  exact sum_misalignedCost_fiber_le he s abs_nonneg c

/-- **Trial sign-vector reading of the incidence energy**: at any sign vector `s`, the incidence
energy is the total budget excess over the point degrees plus twice the misaligned mass. Thus
`2 ν_w(c)` is the exact orientation surplus above the comparison floor `∑ (c_ii - deg_i)`. -/
theorem incidenceEnergy_signVector_eq {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c)
    {s : ι → ℝ} (hs : IsSignVector s) :
    incidenceEnergy c s = ∑ i, (c i i - pointDegree c i) + 2 * misalignedMass s c := by
  rw [incidenceEnergy_eq_signedDirichletForm hc, signedDirichletForm_signVector hs]
  have hsq : ∀ i, (c i i - pointDegree c i) * s i ^ 2 = c i i - pointDegree c i := fun i => by
    rw [hs i, mul_one]
  simp_rw [hsq]
  ring

end Subsample

/-! ### 2. The polar hyperbolic barrier and midpoint quenching at full weight `α = 1, β = 1` -/

/-- Exact hyperbolic product formula for the polar part of `weilKernel`:
`cosh((x + y)/2) - cosh((x - y)/2) = 2 sinh(x/2) sinh(y/2)`. -/
theorem cosh_half_add_sub_cosh_half_sub (x y : ℝ) :
    Real.cosh ((x + y) / 2) - Real.cosh ((x - y) / 2) =
      2 * Real.sinh (x / 2) * Real.sinh (y / 2) := by
  rw [Real.cosh_eq, Real.cosh_eq, Real.sinh_eq, Real.sinh_eq]
  have h1 : (x + y) / 2 = x / 2 + y / 2 := by ring
  have h2 : -(x / 2 + y / 2) = -(x / 2) + -(y / 2) := by ring
  have h3 : (x - y) / 2 = x / 2 + -(y / 2) := by ring
  have h4 : -(x / 2 + -(y / 2)) = -(x / 2) + y / 2 := by ring
  rw [h1, h2, h3, h4, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add]
  ring

/-- The archimedean factor `2 e^{-u/2} / (1 - e^{-2u})` of `weilKernel` is strictly decreasing on
`(0, ∞)`. -/
theorem archimedeanFactor_strictAnti {u u' : ℝ} (hu : 0 < u) (huu : u < u') :
    2 * Real.exp (-u' / 2) / (1 - Real.exp (-2 * u')) <
      2 * Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) := by
  have d1 := RHTower.ArchimedeanKernel.one_sub_exp_neg_two_mul_pos hu
  have d2 : 1 - Real.exp (-2 * u) ≤ 1 - Real.exp (-2 * u') := by
    have := Real.exp_le_exp.2 (by linarith : -2 * u' ≤ -2 * u); linarith
  have n1 : Real.exp (-u' / 2) < Real.exp (-u / 2) := Real.exp_lt_exp.2 (by linarith)
  exact div_lt_div₀ (by linarith) d2 (by positivity) d1

/-- **The polar hyperbolic barrier**: for any distinct positive positions `x ≠ y`, the folded
archimedean–polar kernel satisfies
`weilKernel |x + y| - weilKernel |x - y| < -8 sinh(x/2) sinh(y/2) < 0`. -/
theorem weilKernel_add_sub_weilKernel_sub_lt_neg_eight_sinh {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    RHTower.ArchimedeanKernel.weilKernel |x + y| -
        RHTower.ArchimedeanKernel.weilKernel |x - y| <
      -8 * Real.sinh (x / 2) * Real.sinh (y / 2) := by
  have hd : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 hxy)
  have hs : |x + y| = x + y := abs_of_pos (add_pos hx hy)
  have hds : |x - y| < |x + y| := by
    rw [hs, abs_lt]; constructor <;> linarith
  have harch := archimedeanFactor_strictAnti hd hds
  have hcosh_abs : Real.cosh (|x - y| / 2) = Real.cosh ((x - y) / 2) := by
    rw [← Real.cosh_abs ((x - y) / 2), abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpolar := cosh_half_add_sub_cosh_half_sub x y
  unfold RHTower.ArchimedeanKernel.weilKernel
  rw [hs] at harch ⊢
  rw [hcosh_abs]
  linarith

/-- **Pointwise polar-barrier bound on the odd Weil ledger**: every off-diagonal overlap is strictly
bounded by `β · primeKernel(p_x + p_y) - 8 α sinh(p_x/2) sinh(p_y/2)`. -/
theorem oddFold_weilLedgerKernel_lt_prime_sub_sinh {ι : Type*} [DecidableEq ι]
    {p : ι → ℝ} (hp : ∀ x, 0 < p x) (hinj : Function.Injective p)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (b : ι → ℝ) {x y : ι} (hxy : x ≠ y) :
    oddFold p (weilLedgerKernel α β) b x y <
      β * primeKernel (p x + p y) - 8 * α * Real.sinh (p x / 2) * Real.sinh (p y / 2) := by
  rw [oddFold_weilLedgerKernel hxy, oddFold_offDiag hxy]
  have hbar := weilKernel_add_sub_weilKernel_sub_lt_neg_eight_sinh (hp x) (hp y)
    (fun e => hxy (hinj e))
  have hpr := primeKernel_nonneg (p x - p y)
  nlinarith [mul_lt_mul_of_pos_left hbar hα, mul_nonneg hβ hpr]

/-- **Necessary condition for an anti-aligned overlap at positive archimedean weight**: if
`oddFold p (weilLedgerKernel α β) b x y > 0`, then the polar barrier `8 α sinh(p_x/2) sinh(p_y/2)`
must be strictly smaller than the prime-sum charge `β · primeKernel(p_x + p_y)`. -/
theorem eight_sinh_mul_sinh_lt_primeKernel_of_oddFold_pos {ι : Type*} [DecidableEq ι]
    {p : ι → ℝ} (hp : ∀ x, 0 < p x) (hinj : Function.Injective p)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) {b : ι → ℝ} {x y : ι} (hxy : x ≠ y)
    (hpos : 0 < oddFold p (weilLedgerKernel α β) b x y) :
    8 * α * Real.sinh (p x / 2) * Real.sinh (p y / 2) < β * primeKernel (p x + p y) := by
  have := oddFold_weilLedgerKernel_lt_prime_sub_sinh hp hinj hα hβ b hxy
  linarith

/-- For every real `x ≥ 5`, `weilKernel (log x) + (log x) / √x < -2`. -/
theorem weilKernel_add_log_div_sqrt_lt_neg_two {x : ℝ} (hx : 5 ≤ x) :
    RHTower.ArchimedeanKernel.weilKernel (Real.log x) + Real.log x / Real.sqrt x < -2 := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hs2 : (2 : ℝ) < Real.sqrt x := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hlog : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
  rw [weilKernel_log_eq hx1]
  have hden : 0 < (x ^ 2 - 1) * Real.sqrt x := by nlinarith
  have hcomb : -2 * (x ^ 3 - x - 1) / ((x ^ 2 - 1) * Real.sqrt x) + Real.log x / Real.sqrt x =
      (-2 * (x ^ 3 - x - 1) + (x ^ 2 - 1) * Real.log x) / ((x ^ 2 - 1) * Real.sqrt x) := by
    have : x ^ 2 - 1 ≠ 0 := by nlinarith
    have : Real.sqrt x ≠ 0 := hsx.ne'
    field_simp
  rw [hcomb, div_lt_iff₀ hden]
  have hmul : (x ^ 2 - 1) * Real.log x ≤ (x ^ 2 - 1) * (x - 1) :=
    mul_le_mul_of_nonneg_left hlog (by nlinarith)
  have hlin : (x ^ 2 - 1) * Real.sqrt x * 2 > 4 * (x ^ 2 - 1) := by nlinarith
  nlinarith

/-- **Midpoint quenching at full archimedean–polar weight**: on the midpoint-matched sample
`matchedPos Q` (`½ log(3q/2), ½ log(2q/3)` for primes `q ≥ 5`), every off-diagonal overlap at the
source-faithful full weight `weilLedgerKernel 1 1` is strictly aligned (`< 0`). -/
theorem oddFold_matchedPos_weilLedgerKernel_one_neg {Q : Finset ℕ}
    (hQ : ∀ q ∈ Q, q.Prime ∧ 5 ≤ q) (b : ↥Q × Bool → ℝ) {x y : ↥Q × Bool} (hxy : x ≠ y) :
    oddFold (matchedPos Q) (weilLedgerKernel 1 1) b x y < 0 := by
  by_cases hpart : y = matchedPartner x
  · subst hpart
    rw [oddFold_matchedPartner hQ]
    have h5 := five_le_matched hQ x
    have hq := weilKernel_add_log_div_sqrt_lt_neg_two h5
    have h32 := neg_weilKernel_log_three_halves_lt
    linarith
  · refine oddFold_neg_of_not_primeSum (matchedPos_pos hQ) (matchedPos_injective hQ)
      one_pos zero_le_one b hxy fun n hn => ?_
    exact absurd (eq_matchedPartner_of_exp_eq hQ hxy hn) hpart

/-- **At full archimedean weight `α = 1, β = 1`, the midpoint-matched family `matchedPos Q` is
balanced.** -/
theorem isBalanced_matchedPos_weilLedgerKernel_one {Q : Finset ℕ}
    (hQ : ∀ q ∈ Q, q.Prime ∧ 5 ≤ q) (b : ↥Q × Bool → ℝ) :
    IsBalanced (oddFold (matchedPos Q) (weilLedgerKernel 1 1) b) :=
  isBalanced_of_aligned fun _ _ hxy => (oddFold_matchedPos_weilLedgerKernel_one_neg hQ b hxy).le

/-- **At full archimedean weight `α = 1, β = 1`, the midpoint-matched family `matchedPos Q` has
frustration index `0`.** -/
theorem frustrationIndex_matchedPos_weilLedgerKernel_one_eq_zero {Q : Finset ℕ}
    (hQ : ∀ q ∈ Q, q.Prime ∧ 5 ≤ q) (b : ↥Q × Bool → ℝ) :
    frustrationIndex (oddFold (matchedPos Q) (weilLedgerKernel 1 1) b) = 0 :=
  (isBalanced_iff_frustrationIndex_eq_zero _).1 (isBalanced_matchedPos_weilLedgerKernel_one hQ b)

/-- **At full archimedean weight `α = 1, β = 1`, the midpoint-matched family `matchedPos Q` has
frustration mass `0`.** -/
theorem frustrationMass_matchedPos_weilLedgerKernel_one_eq_zero {Q : Finset ℕ}
    (hQ : ∀ q ∈ Q, q.Prime ∧ 5 ≤ q) (b : ↥Q × Bool → ℝ) :
    frustrationMass (oddFold (matchedPos Q) (weilLedgerKernel 1 1) b) = 0 := by
  refine le_antisymm ?_ (frustrationMass_nonneg _)
  refine (frustrationMass_le isSignVector_one _).trans (le_of_eq ?_)
  unfold misalignedMass
  refine sum_eq_zero fun x _ => sum_eq_zero fun y _ => ?_
  rw [if_neg]
  rintro ⟨hxy, hpos⟩
  have := oddFold_matchedPos_weilLedgerKernel_one_neg hQ b hxy
  linarith

/-! ### 3. Exact frustration index and mass at full weight `α = 1, β = 1` on `primeTrianglePos`,
`packedPrimePos`, and dense multi-triangle packings -/

/-- **Unconditional frustration index of the prime triangle at full archimedean weight `α = 1, β = 1`**:
for every budget `b : Fin 3 → ℝ`, `frustrationIndex = 2`. -/
theorem frustrationIndex_primeTriangle_weilLedgerKernel_one (b : Fin 3 → ℝ) :
    frustrationIndex (oddFold primeTrianglePos (weilLedgerKernel 1 1) b) = 2 := by
  have hsym : IsSymmetricCoupling (oddFold primeTrianglePos (weilLedgerKernel 1 1) b) :=
    oddFold_isSymmetric (weilLedgerKernel_neg 1 1)
  exact le_antisymm (frustrationIndex_le_two_fin3 hsym)
    (two_le_frustrationIndex_of_not_isBalanced hsym
      (oddFold_primeTriangle_weilLedgerKernel_one_not_isBalanced b))

/-- If every off-diagonal overlap of a symmetric coupling `c` on a linearly ordered set has
`|c i j| ≥ m` (`m ≥ 0`) and `c` is not balanced, then `frustrationMass c ≥ 2 m`. -/
theorem two_mul_le_frustrationMass_of_not_isBalanced {ι : Type*} [Fintype ι] [LinearOrder ι]
    {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) (hnb : ¬ IsBalanced c) {m : ℝ} (hm : 0 ≤ m)
    (hmin : ∀ i j, i ≠ j → m ≤ |c i j|) :
    2 * m ≤ frustrationMass c := by
  refine le_ciInf fun ⟨s, hs⟩ => ?_
  have hcard : 2 ≤ misalignedCount s c :=
    (two_le_frustrationIndex_of_not_isBalanced hc hnb).trans (frustrationIndex_le hs c)
  calc 2 * m ≤ (misalignedCount s c : ℝ) * m := by
        have : (2 : ℝ) ≤ misalignedCount s c := by exact_mod_cast hcard
        nlinarith
    _ = ∑ i, ∑ j, (if i ≠ j ∧ 0 < s i * s j * c i j then m else 0) := by
        rw [misalignedCount_eq_cost, misalignedCost, sum_mul]
        refine sum_congr rfl fun i _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun j _ => ?_
        split_ifs <;> ring
    _ ≤ misalignedMass s c := by
        unfold misalignedMass
        refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
        split_ifs with h
        · exact hmin i j h.1
        · exact le_rfl

/-- **Explicit rational bounds on the frustration mass of the source-faithful prime triangle**:
at full weight `α = 1, β = 1`, for every budget `b : Fin 3 → ℝ`,
`2/7 ≤ frustrationMass (oddFold primeTrianglePos (weilLedgerKernel 1 1) b) < 4/5`. -/
theorem frustrationMass_primeTriangle_weilLedgerKernel_one_bounds (b : Fin 3 → ℝ) :
    (2 / 7 : ℝ) ≤ frustrationMass (oddFold primeTrianglePos (weilLedgerKernel 1 1) b) ∧
      frustrationMass (oddFold primeTrianglePos (weilLedgerKernel 1 1) b) < 4 / 5 := by
  set c := oddFold primeTrianglePos (weilLedgerKernel 1 1) b
  have hsym : IsSymmetricCoupling c := oddFold_isSymmetric (weilLedgerKernel_neg 1 1)
  have h01 : c 0 1 < -1 / 7 := (oddFold_primeTriangle_weilLedgerKernel_one_zero_one b).2
  have h20 : c 2 0 < -1 := (oddFold_primeTriangle_weilLedgerKernel_one_two_zero b).2
  have h12_lo : 3 / 20 < c 1 2 := (oddFold_primeTriangle_weilLedgerKernel_one_one_two b).1
  have h12_hi : c 1 2 < 2 / 5 := (oddFold_primeTriangle_weilLedgerKernel_one_one_two b).2
  constructor
  · -- every off-diagonal entry has `|c i j| ≥ 1/7`
    have hmin : ∀ i j : Fin 3, i ≠ j → (1 / 7 : ℝ) ≤ |c i j| := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hij ⊢
      · exact absurd rfl hij
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [hsym 0 2, abs_of_neg (by linarith)]; linarith
      · rw [hsym 1 0, abs_of_neg (by linarith)]; linarith
      · exact absurd rfl hij
      · rw [abs_of_pos (by linarith)]; linarith
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [hsym 2 1, abs_of_pos (by linarith)]; linarith
      · exact absurd rfl hij
    have hge := two_mul_le_frustrationMass_of_not_isBalanced hsym
      (oddFold_primeTriangle_weilLedgerKernel_one_not_isBalanced b) (by norm_num) hmin
    linarith
  · -- at `s = 1`, only `(1, 2)` and `(2, 1)` are positive, giving mass `2 * c 1 2 < 4/5`
    refine lt_of_le_of_lt (frustrationMass_le isSignVector_one c) ?_
    unfold misalignedMass
    have hcond : ∀ i j : Fin 3, (i ≠ j ∧ 0 < (1 : ℝ) * 1 * c i j) ↔
        (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) := by
      intro i j
      rw [one_mul, one_mul]
      exact ⟨fun ⟨hij, hp⟩ => primeTriangle_pos_overlap_iff b hij hp, fun h => by
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨by decide, by linarith⟩
        · rw [hsym 2 1]; exact ⟨by decide, by linarith⟩⟩
    simp_rw [hcond]
    rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [Fin.isValue, Fin.ext_iff]
    norm_num
    rw [hsym 2 1, abs_of_pos (by linarith)]
    linarith

/-- **Dense switching reduction on `packedPrimePos` (`Fin 4`) at full weight `α = 1, β = 1`**:
two anti-aligned prime-sum edges `(1, 2)` and `(1, 3)` share vertex `1` (violating `4D ≤ n`),
giving `misalignedCount 1 = 4`, and switching vertex `1` (`s = ![1, -1, 1, 1]`) trades both
prime-sum edges for the single aligned hub edge `(0, 1)`, reducing the frustration index to `2`. -/
theorem frustrationIndex_packedPrime_weilLedgerKernel_one (b : Fin 4 → ℝ) :
    misalignedCount (fun _ => 1) (oddFold packedPrimePos (weilLedgerKernel 1 1) b) = 4 ∧
      frustrationIndex (oddFold packedPrimePos (weilLedgerKernel 1 1) b) = 2 := by
  set c := oddFold packedPrimePos (weilLedgerKernel 1 1) b
  have hsym : IsSymmetricCoupling c := oddFold_isSymmetric (weilLedgerKernel_neg 1 1)
  have h01 : c 0 1 < -1 / 7 := (oddFold_packedPrime_zero_one b).2
  have h20 : c 2 0 < -1 := (oddFold_packedPrime_two_zero b).2
  have h12 : 3 / 20 < c 1 2 := (oddFold_packedPrime_one_two b).1
  have h13 : 1 / 4 < c 1 3 := (oddFold_packedPrime_one_three b).1
  have h03 : c 0 3 < -2 := (oddFold_packedPrime_zero_three b).2
  have h23 : c 2 3 < -4 := (oddFold_packedPrime_two_three b).2
  constructor
  · -- unswitched misaligned count is 4: `{(1,2), (2,1), (1,3), (3,1)}`
    unfold misalignedCount
    have hset : (univ.filter fun p : Fin 4 × Fin 4 => p.1 ≠ p.2 ∧ 0 < (1 : ℝ) * 1 * c p.1 p.2) =
        {(1, 2), (2, 1), (1, 3), (3, 1)} := by
      ext ⟨x, y⟩
      simp only [mem_filter, mem_univ, true_and, one_mul, mem_insert, mem_singleton, Prod.mk.injEq]
      exact ⟨fun ⟨hxy, hp⟩ => packedPrime_pos_overlap_iff b hxy hp, fun h => by
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨by decide, by linarith⟩
        · rw [hsym 2 1]; exact ⟨by decide, by linarith⟩
        · exact ⟨by decide, by linarith⟩
        · rw [hsym 3 1]; exact ⟨by decide, by linarith⟩⟩
    rw [hset]
    decide
  · apply le_antisymm
    · -- switching vertex 1 (`s = ![1, -1, 1, 1]`) leaves only `(0, 1)` and `(1, 0)` misaligned
      set s : Fin 4 → ℝ := ![1, -1, 1, 1]
      have hs : IsSignVector s := fun i => by fin_cases i <;> norm_num [s]
      refine (frustrationIndex_le hs c).trans ?_
      unfold misalignedCount
      have hsub : (univ.filter fun p : Fin 4 × Fin 4 => p.1 ≠ p.2 ∧ 0 < s p.1 * s p.2 * c p.1 p.2) ⊆
          {(0, 1), (1, 0)} := by
        intro ⟨x, y⟩ hp
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Prod.mk.injEq] at hp ⊢
        obtain ⟨hxy, hpos⟩ := hp
        fin_cases x <;> fin_cases y <;>
          simp only [s, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
            Matrix.tail_cons] at hxy hpos ⊢
        · exact absurd rfl hxy
        · decide
        · rw [hsym 0 2] at hpos; linarith
        · linarith
        · decide
        · exact absurd rfl hxy
        · linarith
        · linarith
        · linarith
        · rw [hsym 2 1] at hpos; linarith
        · exact absurd rfl hxy
        · linarith
        · rw [hsym 3 0] at hpos; linarith
        · rw [hsym 3 1] at hpos; linarith
        · rw [hsym 3 2] at hpos; linarith
        · exact absurd rfl hxy
      exact (card_le_card hsub).trans (by decide)
    · -- lower bound 2 from the embedded `primeTrianglePos` on `{0, 1, 2}`
      let e : Fin 3 → Fin 4 := Fin.castSucc
      have he : Function.Injective e := Fin.castSucc_injective 3
      have hpe : ∀ i : Fin 3, packedPrimePos (e i) = primeTrianglePos i := fun i => by
        fin_cases i <;> rfl
      have hce : (fun i j : Fin 3 => c (e i) (e j)) =
          oddFold primeTrianglePos (weilLedgerKernel 1 1) (fun i => b (e i)) := by
        ext i j
        dsimp only [c]
        by_cases hij : i = j
        · subst hij
          rw [oddFold_diag, oddFold_diag, hpe i]
        · rw [oddFold_offDiag (he.ne hij), oddFold_offDiag hij, hpe i, hpe j]
      have hle := frustrationIndex_comp_injective_le he c
      rw [hce, frustrationIndex_primeTriangle_weilLedgerKernel_one] at hle
      exact hle

/-- **Switching vertex `1` on `packedPrimePos` strictly reduces the misaligned mass**:
the unswitched misaligned mass exceeds `4/5`, whereas `frustrationMass < 4/5`. -/
theorem frustrationMass_packedPrime_weilLedgerKernel_one_lt (b : Fin 4 → ℝ) :
    frustrationMass (oddFold packedPrimePos (weilLedgerKernel 1 1) b) < 4 / 5 ∧
      4 / 5 < misalignedMass (fun _ => 1) (oddFold packedPrimePos (weilLedgerKernel 1 1) b) := by
  set c := oddFold packedPrimePos (weilLedgerKernel 1 1) b
  have hsym : IsSymmetricCoupling c := oddFold_isSymmetric (weilLedgerKernel_neg 1 1)
  have h01_lo : -2 / 5 < c 0 1 := (oddFold_packedPrime_zero_one b).1
  have h01_hi : c 0 1 < -1 / 7 := (oddFold_packedPrime_zero_one b).2
  have h20 : c 2 0 < -1 := (oddFold_packedPrime_two_zero b).2
  have h12 : 3 / 20 < c 1 2 := (oddFold_packedPrime_one_two b).1
  have h13 : 1 / 4 < c 1 3 := (oddFold_packedPrime_one_three b).1
  have h03 : c 0 3 < -2 := (oddFold_packedPrime_zero_three b).2
  have h23 : c 2 3 < -4 := (oddFold_packedPrime_two_three b).2
  constructor
  · set s : Fin 4 → ℝ := ![1, -1, 1, 1]
    have hs : IsSignVector s := fun i => by fin_cases i <;> norm_num [s]
    refine lt_of_le_of_lt (frustrationMass_le hs c) ?_
    unfold misalignedMass
    have hcond : ∀ x y : Fin 4, (x ≠ y ∧ 0 < s x * s y * c x y) ↔
        (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
      intro x y
      constructor
      · rintro ⟨hxy, hpos⟩
        fin_cases x <;> fin_cases y <;>
          simp only [s, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
            Matrix.tail_cons] at hxy hpos
        · exact absurd rfl hxy
        · decide
        · rw [hsym 0 2] at hpos; linarith
        · linarith
        · decide
        · exact absurd rfl hxy
        · linarith
        · linarith
        · linarith
        · rw [hsym 2 1] at hpos; linarith
        · exact absurd rfl hxy
        · linarith
        · rw [hsym 3 0] at hpos; linarith
        · rw [hsym 3 1] at hpos; linarith
        · rw [hsym 3 2] at hpos; linarith
        · exact absurd rfl hxy
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨by decide, by simp [s]; linarith⟩
        · exact ⟨by decide, by simp [s]; rw [hsym 1 0]; linarith⟩
    simp_rw [hcond]
    rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
    simp only [Fin.isValue, Fin.ext_iff]
    norm_num
    rw [hsym 1 0, abs_of_neg (by linarith)]
    linarith
  · unfold misalignedMass
    have hcond : ∀ x y : Fin 4, (x ≠ y ∧ 0 < (1 : ℝ) * 1 * c x y) ↔
        (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨ (x = 1 ∧ y = 3) ∨ (x = 3 ∧ y = 1) := by
      intro x y
      rw [one_mul, one_mul]
      exact ⟨fun ⟨hxy, hp⟩ => packedPrime_pos_overlap_iff b hxy hp, fun h => by
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨by decide, by linarith⟩
        · rw [hsym 2 1]; exact ⟨by decide, by linarith⟩
        · exact ⟨by decide, by linarith⟩
        · rw [hsym 3 1]; exact ⟨by decide, by linarith⟩⟩
    simp_rw [hcond]
    rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
    simp only [Fin.isValue, Fin.ext_iff]
    norm_num
    rw [hsym 2 1, hsym 3 1, abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith

/-- Any perturbed prime triangle with `c 0 1 < -1/7`, `c 2 0 < -1`, and `c 1 2 > 3/20` is
unbalanced, has frustration index `2`, and has frustration mass `≥ 2/7`. -/
theorem frustration_of_perturbed_primeTriangle {c : Fin 3 → Fin 3 → ℝ}
    (hsym : IsSymmetricCoupling c) (h01 : c 0 1 < -1 / 7) (h20 : c 2 0 < -1)
    (h12 : 3 / 20 < c 1 2) :
    frustrationIndex c = 2 ∧ (2 / 7 : ℝ) ≤ frustrationMass c := by
  have hnb : ¬ IsBalanced c := by
    intro hb
    have hco : IsCompleteOverlap c := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hij ⊢
      · exact absurd rfl hij
      · linarith
      · rw [hsym 0 2]; linarith
      · rw [hsym 1 0]; linarith
      · exact absurd rfl hij
      · linarith
      · linarith
      · rw [hsym 2 1]; linarith
      · exact absurd rfl hij
    have hneg := (isBalanced_iff_triangleHolonomy_neg hsym hco).mp hb 0 1 2
      (by decide) (by decide) (by decide)
    unfold triangleHolonomy at hneg
    have hpos : 0 < c 0 1 * c 1 2 * c 2 0 :=
      mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (by linarith) (by linarith)) (by linarith)
    linarith
  refine ⟨le_antisymm (frustrationIndex_le_two_fin3 hsym)
    (two_le_frustrationIndex_of_not_isBalanced hsym hnb), ?_⟩
  have hmin : ∀ i j : Fin 3, i ≠ j → (1 / 7 : ℝ) ≤ |c i j| := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hij ⊢
    · exact absurd rfl hij
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [hsym 0 2, abs_of_neg (by linarith)]; linarith
    · rw [hsym 1 0, abs_of_neg (by linarith)]; linarith
    · exact absurd rfl hij
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [hsym 2 1, abs_of_pos (by linarith)]; linarith
    · exact absurd rfl hij
  have := two_mul_le_frustrationMass_of_not_isBalanced hsym hnb (by norm_num) hmin
  linarith

/-- Perturbed prime triangle positions `(p_0 - t, p_1 + t, p_2 - t)`, preserving the exact prime
sums `q_0 + q_1 = log 2` and `q_1 + q_2 = log 3` and the difference `q_2 - q_0 = p_2 - p_0`. -/
def perturbedPrimeTrianglePos (t : ℝ) (j : Fin 3) : ℝ :=
  if j = 0 then primeTrianglePos 0 - t
  else if j = 1 then primeTrianglePos 1 + t
  else primeTrianglePos 2 - t

theorem perturbedPrimeTrianglePos_zero (t : ℝ) :
    perturbedPrimeTrianglePos t 0 = primeTrianglePos 0 - t := rfl

theorem perturbedPrimeTrianglePos_one (t : ℝ) :
    perturbedPrimeTrianglePos t 1 = primeTrianglePos 1 + t := rfl

theorem perturbedPrimeTrianglePos_two (t : ℝ) :
    perturbedPrimeTrianglePos t 2 = primeTrianglePos 2 - t := rfl

theorem perturbedPrimeTrianglePos_bounds {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 200) :
    (1 / 2 : ℝ) < perturbedPrimeTrianglePos t 0 ∧ perturbedPrimeTrianglePos t 0 < 7 / 10 ∧
    (1 / 25 : ℝ) < perturbedPrimeTrianglePos t 1 ∧ perturbedPrimeTrianglePos t 1 < 1 / 5 ∧
    (9 / 10 : ℝ) < perturbedPrimeTrianglePos t 2 ∧ perturbedPrimeTrianglePos t 2 < 6 / 5 := by
  have h2 := log_two_bounds
  have h3 := log_three_bounds
  have h5 := log_five_bounds
  have hp0_val : primeTrianglePos 0 = (Real.log 2 + Real.log 5 - Real.log 3) / 2 := rfl
  have hp1_val : primeTrianglePos 1 = (Real.log 2 + Real.log 3 - Real.log 5) / 2 := rfl
  have hp2_val : primeTrianglePos 2 = (Real.log 3 + Real.log 5 - Real.log 2) / 2 := rfl
  rw [perturbedPrimeTrianglePos_zero, perturbedPrimeTrianglePos_one,
    perturbedPrimeTrianglePos_two, hp0_val, hp1_val, hp2_val]
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem oddFold_perturbedPrimeTrianglePos_zero_one {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 200)
    (b : Fin 3 → ℝ) :
    oddFold (perturbedPrimeTrianglePos t) (weilLedgerKernel 1 1) b 0 1 =
      RHTower.ArchimedeanKernel.weilKernel (Real.log 2) + Real.log 2 / Real.sqrt 2 -
        RHTower.ArchimedeanKernel.weilKernel
          |(primeTrianglePos 0 - t) - (primeTrianglePos 1 + t)| := by
  have h2 := log_two_bounds
  have h3 := log_three_bounds
  have h5 := log_five_bounds
  have hp0_val : primeTrianglePos 0 = (Real.log 2 + Real.log 5 - Real.log 3) / 2 := rfl
  have hp1_val : primeTrianglePos 1 = (Real.log 2 + Real.log 3 - Real.log 5) / 2 := rfl
  rw [oddFold_weilLedgerKernel (by decide), oddFold_offDiag (by decide)]
  have hsum : perturbedPrimeTrianglePos t 0 + perturbedPrimeTrianglePos t 1 = Real.log 2 := by
    rw [perturbedPrimeTrianglePos_zero, perturbedPrimeTrianglePos_one, hp0_val, hp1_val]; ring
  have hpr0 : primeKernel (perturbedPrimeTrianglePos t 0 - perturbedPrimeTrianglePos t 1) = 0 := by
    apply primeKernel_eq_zero
    intro n
    have h1 : perturbedPrimeTrianglePos t 0 - perturbedPrimeTrianglePos t 1 =
        Real.log 5 - Real.log 3 - 2 * t := by
      rw [perturbedPrimeTrianglePos_zero, perturbedPrimeTrianglePos_one, hp0_val, hp1_val]; ring
    have hpos_diff : 0 < Real.log 5 - Real.log 3 - 2 * t := by linarith
    have h53 : Real.log 5 - Real.log 3 = Real.log (5 / 3) :=
      (Real.log_div (by norm_num) (by norm_num)).symm
    rw [h1, abs_of_pos hpos_diff]
    have hlo : ((1 : ℕ) : ℝ) < Real.exp (Real.log 5 - Real.log 3 - 2 * t) := by
      push_cast; exact Real.one_lt_exp_iff.2 hpos_diff
    have hhi : Real.exp (Real.log 5 - Real.log 3 - 2 * t) < ((1 : ℕ) : ℝ) + 1 := by
      push_cast
      calc Real.exp (Real.log 5 - Real.log 3 - 2 * t)
          < Real.exp (Real.log (5 / 3)) := Real.exp_lt_exp.2 (by linarith)
        _ = 5 / 3 := Real.exp_log (by norm_num)
        _ < 1 + 1 := by norm_num
    exact ne_natCast_of_between (m := 1) hlo hhi n
  have hs2 := primeKernel_log_prime Nat.prime_two
  push_cast at hs2
  rw [hpr0, hsum, abs_of_pos (Real.log_pos (by norm_num)), hs2,
    perturbedPrimeTrianglePos_zero, perturbedPrimeTrianglePos_one]
  ring

theorem oddFold_perturbedPrimeTrianglePos_one_two {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 200)
    (b : Fin 3 → ℝ) :
    oddFold (perturbedPrimeTrianglePos t) (weilLedgerKernel 1 1) b 1 2 =
      RHTower.ArchimedeanKernel.weilKernel (Real.log 3) + Real.log 3 / Real.sqrt 3 -
        RHTower.ArchimedeanKernel.weilKernel
          |(primeTrianglePos 1 + t) - (primeTrianglePos 2 - t)| := by
  have h2 := log_two_bounds
  have h5 := log_five_bounds
  have hp1_val : primeTrianglePos 1 = (Real.log 2 + Real.log 3 - Real.log 5) / 2 := rfl
  have hp2_val : primeTrianglePos 2 = (Real.log 3 + Real.log 5 - Real.log 2) / 2 := rfl
  rw [oddFold_weilLedgerKernel (by decide), oddFold_offDiag (by decide)]
  have hsum : perturbedPrimeTrianglePos t 1 + perturbedPrimeTrianglePos t 2 = Real.log 3 := by
    rw [perturbedPrimeTrianglePos_one, perturbedPrimeTrianglePos_two, hp1_val, hp2_val]; ring
  have hpr0 : primeKernel (perturbedPrimeTrianglePos t 1 - perturbedPrimeTrianglePos t 2) = 0 := by
    apply primeKernel_eq_zero
    intro n
    have h1 : perturbedPrimeTrianglePos t 1 - perturbedPrimeTrianglePos t 2 =
        -(Real.log 5 - Real.log 2 - 2 * t) := by
      rw [perturbedPrimeTrianglePos_one, perturbedPrimeTrianglePos_two, hp1_val, hp2_val]; ring
    have hpos_diff : 0 < Real.log 5 - Real.log 2 - 2 * t := by linarith
    have h52 : Real.log 5 - Real.log 2 = Real.log (5 / 2) :=
      (Real.log_div (by norm_num) (by norm_num)).symm
    rw [h1, abs_neg, abs_of_pos hpos_diff]
    have hlo : ((2 : ℕ) : ℝ) < Real.exp (Real.log 5 - Real.log 2 - 2 * t) := by
      push_cast
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ < Real.exp (Real.log 5 - Real.log 2 - 2 * t) := Real.exp_lt_exp.2 (by linarith)
    have hhi : Real.exp (Real.log 5 - Real.log 2 - 2 * t) < ((2 : ℕ) : ℝ) + 1 := by
      push_cast
      calc Real.exp (Real.log 5 - Real.log 2 - 2 * t)
          < Real.exp (Real.log (5 / 2)) := Real.exp_lt_exp.2 (by linarith)
        _ = 5 / 2 := Real.exp_log (by norm_num)
        _ < 2 + 1 := by norm_num
    exact ne_natCast_of_between (m := 2) hlo hhi n
  have hs3 := primeKernel_log_prime Nat.prime_three
  push_cast at hs3
  rw [hpr0, hsum, abs_of_pos (Real.log_pos (by norm_num)), hs3,
    perturbedPrimeTrianglePos_one, perturbedPrimeTrianglePos_two]
  ring

theorem oddFold_perturbedPrimeTrianglePos_two_zero {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 200)
    (b : Fin 3 → ℝ) :
    oddFold (perturbedPrimeTrianglePos t) (weilLedgerKernel 1 1) b 2 0 =
      RHTower.ArchimedeanKernel.weilKernel (Real.log 5 - 2 * t) -
        RHTower.ArchimedeanKernel.weilKernel |primeTrianglePos 2 - primeTrianglePos 0| := by
  have h2 := log_two_bounds
  have h5 := log_five_bounds
  have hp0_val : primeTrianglePos 0 = (Real.log 2 + Real.log 5 - Real.log 3) / 2 := rfl
  have hp2_val : primeTrianglePos 2 = (Real.log 3 + Real.log 5 - Real.log 2) / 2 := rfl
  rw [oddFold_weilLedgerKernel (by decide), oddFold_offDiag (by decide)]
  have hsum : perturbedPrimeTrianglePos t 2 + perturbedPrimeTrianglePos t 0 =
      Real.log 5 - 2 * t := by
    rw [perturbedPrimeTrianglePos_two, perturbedPrimeTrianglePos_zero, hp2_val, hp0_val]; ring
  have hdiff : perturbedPrimeTrianglePos t 2 - perturbedPrimeTrianglePos t 0 =
      primeTrianglePos 2 - primeTrianglePos 0 := by
    rw [perturbedPrimeTrianglePos_two, perturbedPrimeTrianglePos_zero]; ring
  have hpr_sum : primeKernel (perturbedPrimeTrianglePos t 2 + perturbedPrimeTrianglePos t 0) = 0 := by
    apply primeKernel_eq_zero
    intro n
    rw [hsum, abs_of_pos (by linarith)]
    have hlo : ((4 : ℕ) : ℝ) < Real.exp (Real.log 5 - 2 * t) := by
      push_cast
      have h4 : Real.log 4 < 7 / 5 := by
        have : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]; ring
        linarith
      calc (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
        _ < Real.exp (Real.log 5 - 2 * t) := Real.exp_lt_exp.2 (by linarith)
    have hhi : Real.exp (Real.log 5 - 2 * t) < ((4 : ℕ) : ℝ) + 1 := by
      push_cast
      calc Real.exp (Real.log 5 - 2 * t)
          < Real.exp (Real.log 5) := Real.exp_lt_exp.2 (by linarith)
        _ = 5 := Real.exp_log (by norm_num)
        _ = 4 + 1 := by norm_num
    exact ne_natCast_of_between (m := 4) hlo hhi n
  have hpr_diff : primeKernel (perturbedPrimeTrianglePos t 2 - perturbedPrimeTrianglePos t 0) = 0 := by
    rw [hdiff]
    have hd : primeTrianglePos 2 - primeTrianglePos 0 = Real.log 3 - Real.log 2 := by
      rw [hp2_val, hp0_val]; ring
    rw [hd]
    exact primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 1)
      (by norm_num) (by norm_num)
  rw [hpr_sum, hpr_diff, hsum, hdiff, abs_of_pos (by linarith)]
  ring

theorem exists_delta_perturbedPrimeTrianglePos_frustrated :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 200 → t < δ₀ → ∀ b : Fin 3 → ℝ,
      frustrationIndex (oddFold (perturbedPrimeTrianglePos t) (weilLedgerKernel 1 1) b) = 2 ∧
        (2 / 7 : ℝ) ≤
          frustrationMass (oddFold (perturbedPrimeTrianglePos t) (weilLedgerKernel 1 1) b) := by
  have h2 := log_two_bounds
  have h3 := log_three_bounds
  have h5 := log_five_bounds
  have hp0_val : primeTrianglePos 0 = (Real.log 2 + Real.log 5 - Real.log 3) / 2 := rfl
  have hp1_val : primeTrianglePos 1 = (Real.log 2 + Real.log 3 - Real.log 5) / 2 := rfl
  have hp2_val : primeTrianglePos 2 = (Real.log 3 + Real.log 5 - Real.log 2) / 2 := rfl
  have hd01 : (0 : ℝ) < |primeTrianglePos 0 - primeTrianglePos 1| := abs_pos.2 (by linarith)
  have hd12 : (0 : ℝ) < |primeTrianglePos 1 - primeTrianglePos 2| := abs_pos.2 (by linarith)
  have hcontK : ∀ u > (0 : ℝ), ContinuousAt RHTower.ArchimedeanKernel.weilKernel u := by
    intro u hu
    unfold RHTower.ArchimedeanKernel.weilKernel
    have hne : 1 - Real.exp (-2 * u) ≠ 0 :=
      (RHTower.ArchimedeanKernel.one_sub_exp_neg_two_mul_pos hu).ne'
    fun_prop (disch := assumption)
  have hK01 : RHTower.ArchimedeanKernel.weilKernel (Real.log 2) + Real.log 2 / Real.sqrt 2 -
      RHTower.ArchimedeanKernel.weilKernel |primeTrianglePos 0 - primeTrianglePos 1| < -1 / 7 := by
    have := (oddFold_primeTriangle_weilLedgerKernel_one_zero_one 0).2
    rw [oddFold_weilLedgerKernel (by decide), oddFold_offDiag (by decide)] at this
    have hsum : primeTrianglePos 0 + primeTrianglePos 1 = Real.log 2 := by
      rw [hp0_val, hp1_val]; ring
    have hd0 : primeKernel (primeTrianglePos 0 - primeTrianglePos 1) = 0 := by
      have hdiff : primeTrianglePos 0 - primeTrianglePos 1 = Real.log 5 - Real.log 3 := by
        rw [hp0_val, hp1_val]; ring
      rw [hdiff]
      exact primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 1)
        (by norm_num) (by norm_num)
    have hs2 := primeKernel_log_prime Nat.prime_two
    push_cast at hs2
    rw [hsum, abs_of_pos (Real.log_pos (by norm_num)), hs2, hd0] at this
    linarith
  have hK12 : (3 / 20 : ℝ) < RHTower.ArchimedeanKernel.weilKernel (Real.log 3) +
      Real.log 3 / Real.sqrt 3 -
      RHTower.ArchimedeanKernel.weilKernel |primeTrianglePos 1 - primeTrianglePos 2| := by
    have := (oddFold_primeTriangle_weilLedgerKernel_one_one_two 0).1
    rw [oddFold_weilLedgerKernel (by decide), oddFold_offDiag (by decide)] at this
    have hsum : primeTrianglePos 1 + primeTrianglePos 2 = Real.log 3 := by
      rw [hp1_val, hp2_val]; ring
    have hd0 : primeKernel (primeTrianglePos 1 - primeTrianglePos 2) = 0 := by
      have hdiff : primeTrianglePos 1 - primeTrianglePos 2 = -(Real.log 5 - Real.log 2) := by
        rw [hp1_val, hp2_val]; ring
      rw [hdiff, primeKernel_neg]
      exact primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 2)
        (by norm_num) (by norm_num)
    have hs3 := primeKernel_log_prime Nat.prime_three
    push_cast at hs3
    rw [hsum, abs_of_pos (Real.log_pos (by norm_num)), hs3, hd0] at this
    linarith
  have hK20 : RHTower.ArchimedeanKernel.weilKernel (Real.log 5) -
      RHTower.ArchimedeanKernel.weilKernel |primeTrianglePos 2 - primeTrianglePos 0| < -1 := by
    have := (oddFold_primeTriangle_weilLedgerKernel_one_two_zero 0).2
    rw [oddFold_weilLedgerKernel (by decide), oddFold_offDiag (by decide)] at this
    have hsum : primeTrianglePos 2 + primeTrianglePos 0 = Real.log 5 := by
      rw [hp2_val, hp0_val]; ring
    have hd0 : primeKernel (primeTrianglePos 2 - primeTrianglePos 0) = 0 := by
      have hdiff : primeTrianglePos 2 - primeTrianglePos 0 = Real.log 3 - Real.log 2 := by
        rw [hp2_val, hp0_val]; ring
      rw [hdiff]
      exact primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 1)
        (by norm_num) (by norm_num)
    have hs5 := primeKernel_log_prime Nat.prime_five
    push_cast at hs5
    have hpos5 : (0 : ℝ) < Real.log 5 / Real.sqrt 5 :=
      div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.2 (by norm_num))
    rw [hsum, abs_of_pos (Real.log_pos (by norm_num)), hs5, hd0] at this
    linarith
  set F01 : ℝ → ℝ := fun t => RHTower.ArchimedeanKernel.weilKernel (Real.log 2) +
    Real.log 2 / Real.sqrt 2 -
    RHTower.ArchimedeanKernel.weilKernel |(primeTrianglePos 0 - t) - (primeTrianglePos 1 + t)|
  set F12 : ℝ → ℝ := fun t => RHTower.ArchimedeanKernel.weilKernel (Real.log 3) +
    Real.log 3 / Real.sqrt 3 -
    RHTower.ArchimedeanKernel.weilKernel |(primeTrianglePos 1 + t) - (primeTrianglePos 2 - t)|
  set F20 : ℝ → ℝ := fun t => RHTower.ArchimedeanKernel.weilKernel (Real.log 5 - 2 * t) -
    RHTower.ArchimedeanKernel.weilKernel |primeTrianglePos 2 - primeTrianglePos 0|
  have hc01 : ContinuousAt F01 0 := by
    refine continuousAt_const.sub ?_
    change ContinuousAt (RHTower.ArchimedeanKernel.weilKernel ∘
      fun t : ℝ => |(primeTrianglePos 0 - t) - (primeTrianglePos 1 + t)|) 0
    refine ContinuousAt.comp (by simpa using hcontK _ hd01) ?_
    fun_prop
  have hc12 : ContinuousAt F12 0 := by
    refine continuousAt_const.sub ?_
    change ContinuousAt (RHTower.ArchimedeanKernel.weilKernel ∘
      fun t : ℝ => |(primeTrianglePos 1 + t) - (primeTrianglePos 2 - t)|) 0
    refine ContinuousAt.comp (by simpa using hcontK _ hd12) ?_
    fun_prop
  have hc20 : ContinuousAt F20 0 := by
    have h50 : 0 < Real.log 5 - 2 * (0 : ℝ) := by simp [Real.log_pos (by norm_num : (1 : ℝ) < 5)]
    refine ContinuousAt.sub ?_ continuousAt_const
    change ContinuousAt (RHTower.ArchimedeanKernel.weilKernel ∘ fun t : ℝ => Real.log 5 - 2 * t) 0
    refine ContinuousAt.comp (hcontK _ h50) ?_
    fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), F01 t < -1 / 7 ∧ 3 / 20 < F12 t ∧ F20 t < -1 := by
    refine ((hc01.eventually (gt_mem_nhds (by simpa [F01] using hK01))).and
      ((hc12.eventually (lt_mem_nhds (by simpa [F12] using hK12))).and
        (hc20.eventually (gt_mem_nhds (by simpa [F20] using hK20)))))
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ₀, hδ₀, fun t ht0 ht_le ht_lt b => ?_⟩
  have ht_δ : dist t 0 < δ₀ := by rwa [Real.dist_eq, sub_zero, abs_of_pos ht0]
  obtain ⟨hF01, hF12, hF20⟩ := hball ht_δ
  have hsym : IsSymmetricCoupling (oddFold (perturbedPrimeTrianglePos t) (weilLedgerKernel 1 1) b) :=
    oddFold_isSymmetric (weilLedgerKernel_neg 1 1)
  have h01 : oddFold (perturbedPrimeTrianglePos t) (weilLedgerKernel 1 1) b 0 1 < -1 / 7 := by
    rw [oddFold_perturbedPrimeTrianglePos_zero_one ht0 ht_le b]; exact hF01
  have h12 : 3 / 20 < oddFold (perturbedPrimeTrianglePos t) (weilLedgerKernel 1 1) b 1 2 := by
    rw [oddFold_perturbedPrimeTrianglePos_one_two ht0 ht_le b]; exact hF12
  have h20 : oddFold (perturbedPrimeTrianglePos t) (weilLedgerKernel 1 1) b 2 0 < -1 := by
    rw [oddFold_perturbedPrimeTrianglePos_two_zero ht0 ht_le b]; exact hF20
  exact frustration_of_perturbed_primeTriangle hsym h01 h20 h12

/-- **Dense multi-triangle packing at full archimedean weight `α = 1, β = 1`**: for every
multiplicity `M ≥ 1` there is an injective `3M`-point sample `p : Fin M × Fin 3 → ℝ` in
`(0, log 5]` whose odd Weil ledger at `α = 1, β = 1` has `frustrationIndex ≥ 2M` and
`frustrationMass ≥ (2/7) M` for every budget `b`. -/
theorem exists_dense_primeTriangle_packing_weilLedgerKernel_one (M : ℕ) :
    ∃ p : Fin M × Fin 3 → ℝ, Function.Injective p ∧
      (∀ x, 0 < p x ∧ p x ≤ Real.log 5) ∧
      ∀ b : Fin M × Fin 3 → ℝ,
        2 * M ≤ frustrationIndex (oddFold p (weilLedgerKernel 1 1) b) ∧
          (2 / 7 : ℝ) * M ≤ frustrationMass (oddFold p (weilLedgerKernel 1 1) b) := by
  obtain ⟨δ₀, hδ₀, hfr⟩ := exists_delta_perturbedPrimeTrianglePos_frustrated
  set ε : ℝ := min (δ₀ / 2) (1 / 200)
  have hε : 0 < ε := lt_min (half_pos hδ₀) (by norm_num)
  have hε_le : ε ≤ 1 / 200 := min_le_right _ _
  have hε_lt : ε < δ₀ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ₀)
  let t : Fin M → ℝ := fun r => ε * ((r : ℕ) + 1 : ℝ) / ((M : ℝ) + 1)
  have ht_pos : ∀ r : Fin M, 0 < t r := fun r => by positivity
  have ht_le : ∀ r : Fin M, t r ≤ ε := fun r => by
    have hr_nat : (r : ℕ) + 1 ≤ M + 1 := by omega
    have hr : ((r : ℕ) + 1 : ℝ) ≤ (M : ℝ) + 1 := by exact_mod_cast hr_nat
    exact div_le_of_le_mul₀ (by positivity) hε.le (mul_le_mul_of_nonneg_left hr hε.le)
  have ht_inj : Function.Injective t := fun r₁ r₂ h => by
    have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have h1 : ε * ((r₁ : ℕ) + 1 : ℝ) = ε * ((r₂ : ℕ) + 1 : ℝ) := (div_left_inj' hM1.ne').1 h
    have h2 : ((r₁ : ℕ) + 1 : ℝ) = ((r₂ : ℕ) + 1 : ℝ) := mul_left_cancel₀ hε.ne' h1
    exact Fin.ext (by exact_mod_cast add_right_cancel h2)
  let p : Fin M × Fin 3 → ℝ := fun x => perturbedPrimeTrianglePos (t x.1) x.2
  have hp_inj : Function.Injective p := by
    rintro ⟨r₁, j₁⟩ ⟨r₂, j₂⟩ h
    have b1 := perturbedPrimeTrianglePos_bounds (ht_pos r₁) ((ht_le r₁).trans hε_le)
    have b2 := perturbedPrimeTrianglePos_bounds (ht_pos r₂) ((ht_le r₂).trans hε_le)
    dsimp [p] at h
    fin_cases j₁ <;> fin_cases j₂ <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at h ⊢
    · rw [perturbedPrimeTrianglePos_zero, perturbedPrimeTrianglePos_zero] at h
      exact Prod.ext (ht_inj (by linarith)) rfl
    · exfalso; linarith
    · exfalso; linarith
    · exfalso; linarith
    · rw [perturbedPrimeTrianglePos_one, perturbedPrimeTrianglePos_one] at h
      exact Prod.ext (ht_inj (by linarith)) rfl
    · exfalso; linarith
    · exfalso; linarith
    · exfalso; linarith
    · rw [perturbedPrimeTrianglePos_two, perturbedPrimeTrianglePos_two] at h
      exact Prod.ext (ht_inj (by linarith)) rfl
  refine ⟨p, hp_inj, fun ⟨r, j⟩ => ?_, fun b => ?_⟩
  · have br := perturbedPrimeTrianglePos_bounds (ht_pos r) ((ht_le r).trans hε_le)
    have h5 := log_five_bounds.1
    dsimp [p]
    fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      exact ⟨by linarith, by linarith⟩
  · have hfib : ∀ r : Fin M,
        (fun j₁ j₂ : Fin 3 => oddFold p (weilLedgerKernel 1 1) b (id (r, j₁)) (id (r, j₂))) =
          oddFold (perturbedPrimeTrianglePos (t r)) (weilLedgerKernel 1 1) (fun j => b (r, j)) := by
      intro r
      ext j₁ j₂
      by_cases hj : j₁ = j₂
      · subst hj; simp [oddFold_diag, p]
      · have hne : (r, j₁) ≠ (r, j₂) := fun h => hj (Prod.ext_iff.1 h).2
        simp [oddFold_offDiag hne, oddFold_offDiag hj, p]
    have hfr_r : ∀ r : Fin M,
        frustrationIndex (fun j₁ j₂ : Fin 3 =>
          oddFold p (weilLedgerKernel 1 1) b (id (r, j₁)) (id (r, j₂))) = 2 ∧
        (2 / 7 : ℝ) ≤ frustrationMass (fun j₁ j₂ : Fin 3 =>
          oddFold p (weilLedgerKernel 1 1) b (id (r, j₁)) (id (r, j₂))) := fun r => by
      rw [hfib r]
      exact hfr (t r) (ht_pos r) ((ht_le r).trans hε_le) ((ht_le r).trans_lt hε_lt) _
    constructor
    · have hsum := sum_frustrationIndex_fiber_le (e := id) Function.injective_id
        (oddFold p (weilLedgerKernel 1 1) b)
      have heq : ∑ r : Fin M, frustrationIndex (fun j₁ j₂ : Fin 3 =>
          oddFold p (weilLedgerKernel 1 1) b (id (r, j₁)) (id (r, j₂))) = 2 * M := by
        rw [sum_congr rfl fun r _ => (hfr_r r).1, sum_const, Finset.card_fin, smul_eq_mul, mul_comm]
      exact heq ▸ hsum
    · have hsum := sum_frustrationMass_fiber_le (e := id) Function.injective_id
        (oddFold p (weilLedgerKernel 1 1) b)
      have hle : (2 / 7 : ℝ) * M ≤ ∑ r : Fin M, frustrationMass (fun j₁ j₂ : Fin 3 =>
          oddFold p (weilLedgerKernel 1 1) b (id (r, j₁)) (id (r, j₂))) := by
        calc (2 / 7 : ℝ) * M = ∑ _ : Fin M, (2 / 7 : ℝ) := by
              rw [sum_const, Finset.card_fin, nsmul_eq_mul, mul_comm]
          _ ≤ ∑ r : Fin M, frustrationMass (fun j₁ j₂ : Fin 3 =>
              oddFold p (weilLedgerKernel 1 1) b (id (r, j₁)) (id (r, j₂))) :=
              sum_le_sum fun r _ => (hfr_r r).2
      exact hle.trans hsum

/-! ### 4. Collar-skimming survival at full weight `α = 1, β = 1` -/

/-- For any integer `N ≥ 1`, `log(N + 1) - log N ≥ 1 / (N + 1)`. -/
theorem one_div_add_one_le_log_add_one_sub_log {N : ℕ} (hN : 1 ≤ N) :
    1 / ((N : ℝ) + 1) ≤ Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hN0 hN1)
  rw [Real.log_div hN0.ne' hN1.ne'] at h
  have hsub : (N : ℝ) / ((N : ℝ) + 1) - 1 = -(1 / ((N : ℝ) + 1)) := by field_simp; ring
  linarith

/-- **Elementary logarithmic isolation lemma**: for `N ≥ 1` and `0 < |t| < 1 / (N + 1)`,
`exp(log N + t)` is never a natural number. -/
theorem exp_log_nat_add_ne_nat {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht0 : t ≠ 0)
    (ht : |t| < 1 / ((N : ℝ) + 1)) (n : ℕ) :
    Real.exp (Real.log (N : ℝ) + t) ≠ (n : ℝ) := by
  intro heq
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : 0 < n := by
    by_contra h0
    have hn_eq : n = 0 := by omega
    subst hn_eq
    push_cast at heq
    have := Real.exp_pos (Real.log (N : ℝ) + t)
    linarith
  have hlog : Real.log (N : ℝ) + t = Real.log (n : ℝ) := by
    rw [← Real.log_exp (Real.log (N : ℝ) + t), heq]
  have habs := abs_lt.1 ht
  rcases lt_trichotomy n N with hlt | rfl | hgt
  · have hn1 : n + 1 ≤ N := hlt
    have hle1 : Real.log ((n : ℝ) + 1) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hn1)
    have hgap := one_div_add_one_le_log_add_one_sub_log hn0
    have hinv : 1 / ((N : ℝ) + 1) < 1 / ((n : ℝ) + 1) :=
      one_div_lt_one_div_of_lt (by positivity) (by exact_mod_cast Nat.add_lt_add_right hlt 1)
    linarith
  · exact ht0 (by linarith)
  · have hN1 : N + 1 ≤ n := hgt
    have hle1 : Real.log ((N : ℝ) + 1) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hN1)
    have hgap := one_div_add_one_le_log_add_one_sub_log hN
    linarith

/-- **The collar-skimming configuration**: for an index type `I`, prime map `π : I → ℕ`, and small
shifts `δ : I → ℝ`, places the lower point at `δ i` and the upper point at `log(π i) - δ i`. -/
def collarPos {I : Type*} (π : I → ℕ) (δ : I → ℝ) (x : I × Bool) : ℝ :=
  if x.2 then Real.log (π x.1 : ℝ) - δ x.1 else δ x.1

/-- The partner of a collar-skimming point. -/
def collarPartner {I : Type*} (x : I × Bool) : I × Bool := (x.1, !x.2)

theorem collarPartner_ne {I : Type*} (x : I × Bool) : x ≠ collarPartner x := by
  intro h
  have h2 : x.2 = !x.2 := congrArg Prod.snd h
  cases hb : x.2 <;> rw [hb] at h2 <;> exact absurd h2 (by decide)

theorem collarPos_add_partner {I : Type*} {π : I → ℕ} {δ : I → ℝ} (x : I × Bool) :
    collarPos π δ x + collarPos π δ (collarPartner x) = Real.log (π x.1 : ℝ) := by
  unfold collarPos collarPartner
  cases x.2 <;> simp

section Collar

variable {I : Type*} [Fintype I] [DecidableEq I] {π : I → ℕ} {δ : I → ℝ}

omit [Fintype I] [DecidableEq I] in
theorem abs_collarPos_sub_partner (hπ : ∀ i, 2 ≤ π i) (_hδ0 : ∀ i, 0 < δ i)
    (hδ : ∀ i, 2 * δ i < 1 / ((π i : ℝ) + 1)) (x : I × Bool) :
    |collarPos π δ x - collarPos π δ (collarPartner x)| =
      Real.log (π x.1 : ℝ) - 2 * δ x.1 := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [log_two_bounds.1]
  have hπ2 : Real.log 2 ≤ Real.log (π x.1 : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hπ x.1)
  have h2 : 2 * δ x.1 < 1 / ((π x.1 : ℝ) + 1) := hδ x.1
  have hinv : 1 / ((π x.1 : ℝ) + 1) ≤ 1 / 3 := by
    refine one_div_le_one_div_of_le (by norm_num) ?_
    have : (2 : ℝ) ≤ π x.1 := by exact_mod_cast hπ x.1
    linarith
  have hpos : 0 < Real.log (π x.1 : ℝ) - 2 * δ x.1 := by linarith
  unfold collarPos collarPartner
  cases x.2 <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  · rw [show δ x.1 - (Real.log (π x.1 : ℝ) - δ x.1) = -(Real.log (π x.1 : ℝ) - 2 * δ x.1) by ring,
      abs_neg, abs_of_pos hpos]
  · rw [show Real.log (π x.1 : ℝ) - δ x.1 - δ x.1 = Real.log (π x.1 : ℝ) - 2 * δ x.1 by ring,
      abs_of_pos hpos]

omit [Fintype I] [DecidableEq I] in
theorem collarPos_pos (hπ : ∀ i, 2 ≤ π i) (hδ0 : ∀ i, 0 < δ i)
    (hδ : ∀ i, 2 * δ i < 1 / ((π i : ℝ) + 1)) (x : I × Bool) :
    0 < collarPos π δ x := by
  unfold collarPos
  split_ifs with h
  · have := abs_collarPos_sub_partner hπ hδ0 hδ x
    have h0 := hδ0 x.1
    have habs := abs_nonneg (collarPos π δ x - collarPos π δ (collarPartner x))
    linarith
  · exact hδ0 x.1

omit [Fintype I] in
theorem collarPos_injective (hπ : ∀ i, 2 ≤ π i) (hδ0 : ∀ i, 0 < δ i)
    (hδ_inj : Function.Injective δ)
    (hδ : ∀ i, 2 * δ i < 1 / ((π i : ℝ) + 1)) :
    Function.Injective (collarPos π δ) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [log_two_bounds.1]
  have h_lt_quarter : ∀ k, δ k < 1 / 6 := fun k => by
    have hk : (2 : ℝ) ≤ π k := by exact_mod_cast hπ k
    have hinv : 1 / ((π k : ℝ) + 1) ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith [hδ k]
  have h_gt_third : ∀ k, 1 / 3 < Real.log (π k : ℝ) - δ k := fun k => by
    have hk : Real.log 2 ≤ Real.log (π k : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hπ k)
    have := h_lt_quarter k
    linarith
  unfold collarPos at h
  cases a <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  · exact Prod.ext (hδ_inj h) rfl
  · exfalso; linarith [h_lt_quarter i, h_gt_third j]
  · exfalso; linarith [h_gt_third i, h_lt_quarter j]
  · by_cases hij : i = j
    · exact Prod.ext hij rfl
    · exfalso
      -- WLOG `π i ≤ π j` or `π j ≤ π i`
      have h_step : ∀ u v : I, u ≠ v → π u ≤ π v →
          Real.log (π u : ℝ) - δ u ≠ Real.log (π v : ℝ) - δ v := by
        intro u v huv hpuv heq
        have h_exp : Real.exp (Real.log (π u : ℝ) + (δ v - δ u)) = (π v : ℝ) := by
          have hpos : (0 : ℝ) < π v := by exact_mod_cast (by have := hπ v; omega : 0 < π v)
          rw [show Real.log (π u : ℝ) + (δ v - δ u) = Real.log (π v : ℝ) by linarith,
            Real.exp_log hpos]
        have hne : δ v - δ u ≠ 0 := sub_ne_zero.2 fun e => huv (hδ_inj e.symm)
        have hpu : (2 : ℝ) ≤ π u := by exact_mod_cast hπ u
        have hpuv_r : ((π u : ℝ) + 1) ≤ (π v : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hpuv 1
        have hinv : 1 / ((π v : ℝ) + 1) ≤ 1 / ((π u : ℝ) + 1) :=
          one_div_le_one_div_of_le (by linarith) hpuv_r
        have habs : |δ v - δ u| < 1 / ((π u : ℝ) + 1) := by
          rw [abs_lt]
          have := hδ u; have := hδ v; have := hδ0 u; have := hδ0 v
          constructor <;> linarith
        exact exp_log_nat_add_ne_nat (by have := hπ u; omega) hne habs (π v) h_exp
      rcases le_total (π i) (π j) with hpij | hpji
      · exact h_step i j hij hpij h
      · exact h_step j i (Ne.symm hij) hpji h.symm

omit [Fintype I] in
/-- **Prime-sum isolation on `collarPos`**: when the collar shifts `δ i` are injective and bounded
by `1 / (2 (π i · π j + 1))`, the ONLY pairs `x ≠ y` whose positions sum to the logarithm of a
natural number are the partner pairs `y = collarPartner x`. -/
theorem eq_collarPartner_of_exp_eq (hπ : ∀ i, 2 ≤ π i) (hδ0 : ∀ i, 0 < δ i)
    (hδ_inj : Function.Injective δ)
    (hδ : ∀ i j, δ i + δ j < 1 / (((π i * π j : ℕ) : ℝ) + 1))
    {x y : I × Bool} (hxy : x ≠ y) {n : ℕ}
    (hn : Real.exp (collarPos π δ x + collarPos π δ y) = n) :
    y = collarPartner x := by
  obtain ⟨i, a⟩ := x
  obtain ⟨j, b⟩ := y
  by_cases hij : i = j
  · subst hij
    cases a <;> cases b <;> simp_all [collarPartner]
  · exfalso
    have h_ij := hδ i j
    have h_ii := hδ i i
    have h_jj := hδ j j
    have hπi : (2 : ℝ) ≤ π i := by exact_mod_cast hπ i
    have hπj : (2 : ℝ) ≤ π j := by exact_mod_cast hπ j
    have hprod_ge : ((π i : ℝ) + 1) ≤ ((π i * π j : ℕ) : ℝ) + 1 := by
      push_cast; nlinarith
    have hprod_ge_j : ((π j : ℝ) + 1) ≤ ((π i * π j : ℕ) : ℝ) + 1 := by
      push_cast; nlinarith
    cases a <;> cases b <;>
      simp only [collarPos, Bool.false_eq_true, ↓reduceIte] at hn
    · -- Two lower points: `δ i + δ j = log 1 + (δ i + δ j)`
      have h1 : Real.exp (Real.log ((1 : ℕ) : ℝ) + (δ i + δ j)) = (n : ℝ) := by
        simpa [Real.log_one] using hn
      have hlt : |δ i + δ j| < 1 / (((1 : ℕ) : ℝ) + 1) := by
        rw [abs_of_pos (add_pos (hδ0 i) (hδ0 j))]
        have : (((1 : ℕ) : ℝ) + 1) ≤ ((π i * π j : ℕ) : ℝ) + 1 := by push_cast; nlinarith
        exact h_ij.trans_le (one_div_le_one_div_of_le (by norm_num) this)
      exact exp_log_nat_add_ne_nat le_rfl (add_pos (hδ0 i) (hδ0 j)).ne' hlt n h1
    · -- Lower + upper: `log(π j) + (δ i - δ j)`
      have h1 : Real.exp (Real.log (π j : ℝ) + (δ i - δ j)) = (n : ℝ) := by
        rw [show Real.log (π j : ℝ) + (δ i - δ j) = δ i + (Real.log (π j : ℝ) - δ j) by ring]
        exact hn
      have hne : δ i - δ j ≠ 0 := sub_ne_zero.2 fun e => hij (hδ_inj e)
      have hlt : |δ i - δ j| < 1 / ((π j : ℝ) + 1) := by
        have h_sum : δ i + δ j < 1 / ((π j : ℝ) + 1) :=
          h_ij.trans_le (one_div_le_one_div_of_le (by linarith) hprod_ge_j)
        rw [abs_lt]
        have := hδ0 i; have := hδ0 j
        constructor <;> linarith
      exact exp_log_nat_add_ne_nat (by have := hπ j; omega) hne hlt n h1
    · -- Upper + lower: `log(π i) + (δ j - δ i)`
      have h1 : Real.exp (Real.log (π i : ℝ) + (δ j - δ i)) = (n : ℝ) := by
        rw [show Real.log (π i : ℝ) + (δ j - δ i) = Real.log (π i : ℝ) - δ i + δ j by ring]
        exact hn
      have hne : δ j - δ i ≠ 0 := sub_ne_zero.2 fun e => hij (hδ_inj e.symm)
      have hlt : |δ j - δ i| < 1 / ((π i : ℝ) + 1) := by
        have h_sum : δ i + δ j < 1 / ((π i : ℝ) + 1) :=
          h_ij.trans_le (one_div_le_one_div_of_le (by linarith) hprod_ge)
        rw [abs_lt]
        have := hδ0 i; have := hδ0 j
        constructor <;> linarith
      exact exp_log_nat_add_ne_nat (by have := hπ i; omega) hne hlt n h1
    · -- Two upper points: `log(π i · π j) - (δ i + δ j)`
      have hlog_mul : Real.log ((π i * π j : ℕ) : ℝ) = Real.log (π i : ℝ) + Real.log (π j : ℝ) := by
        push_cast
        exact Real.log_mul (by linarith) (by linarith)
      have h1 : Real.exp (Real.log ((π i * π j : ℕ) : ℝ) + -(δ i + δ j)) = (n : ℝ) := by
        rw [hlog_mul, show Real.log (π i : ℝ) + Real.log (π j : ℝ) + -(δ i + δ j) =
          Real.log (π i : ℝ) - δ i + (Real.log (π j : ℝ) - δ j) by ring]
        exact hn
      have hne : -(δ i + δ j) ≠ 0 := neg_ne_zero.2 (add_pos (hδ0 i) (hδ0 j)).ne'
      have hlt : |-(δ i + δ j)| < 1 / (((π i * π j : ℕ) : ℝ) + 1) := by
        rw [abs_neg, abs_of_pos (add_pos (hδ0 i) (hδ0 j))]
        exact h_ij
      have hN : 1 ≤ π i * π j := by have := hπ i; have := hπ j; nlinarith
      exact exp_log_nat_add_ne_nat hN hne hlt n h1

omit [Fintype I] in
/-- The partner overlap on `collarPos`:
`α (K(log(π i)) - K(log(π i) - 2 δ i)) + β log(π i) / √(π i)`. -/
theorem oddFold_collarPartner (hπ : ∀ i, (π i).Prime) (hδ0 : ∀ i, 0 < δ i)
    (hδ : ∀ i, 2 * δ i < 1 / ((π i : ℝ) + 1)) {α β : ℝ} (b : I × Bool → ℝ) (x : I × Bool) :
    oddFold (collarPos π δ) (weilLedgerKernel α β) b x (collarPartner x) =
      α * (RHTower.ArchimedeanKernel.weilKernel (Real.log (π x.1 : ℝ)) -
        RHTower.ArchimedeanKernel.weilKernel (Real.log (π x.1 : ℝ) - 2 * δ x.1)) +
      β * (Real.log (π x.1 : ℝ) / Real.sqrt (π x.1 : ℝ)) := by
  have hπ2 : ∀ i, 2 ≤ π i := fun i => (hπ i).two_le
  have hne := collarPartner_ne x
  have hpi_gt : (1 : ℝ) < π x.1 := by exact_mod_cast (hπ x.1).one_lt
  rw [oddFold_weilLedgerKernel hne, oddFold_offDiag hne, collarPos_add_partner,
    abs_collarPos_sub_partner hπ2 hδ0 hδ, abs_of_pos (Real.log_pos hpi_gt),
    primeKernel_log_prime (hπ x.1)]
  have h0 : primeKernel (collarPos π δ x - collarPos π δ (collarPartner x)) = 0 := by
    apply primeKernel_eq_zero
    intro n
    rw [abs_collarPos_sub_partner hπ2 hδ0 hδ]
    have hlt : |-2 * δ x.1| < 1 / ((π x.1 : ℝ) + 1) := by
      rw [abs_of_neg (by linarith [hδ0 x.1])]
      linarith [hδ x.1]
    rw [show Real.log (π x.1 : ℝ) - 2 * δ x.1 = Real.log (π x.1 : ℝ) + (-2 * δ x.1) by ring]
    exact exp_log_nat_add_ne_nat (by have := hπ2 x.1; omega)
      (by linarith [hδ0 x.1]) hlt n
  rw [h0]
  ring

/-- **Collar-skimming survival at full archimedean weight**: for any finite index set `I`
(`2 ≤ card I`), prime map `π : I → ℕ`, and **every** fixed `α > 0, β > 0` (including the
source-faithful full weight `α = 1, β = 1`), there is `ε₀ > 0` such that every injective
`δ : I → (0, ε₀)` gives `collarPos π δ` frustration index `2 · card I`. -/
theorem frustrationIndex_collarPos_fullWeight (hcard : 2 ≤ Fintype.card I)
    (hπ : ∀ i, (π i).Prime) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ δ : I → ℝ, Function.Injective δ →
      (∀ i, 0 < δ i ∧ δ i < ε₀) → ∀ b : I × Bool → ℝ,
        frustrationIndex (oddFold (collarPos π δ) (weilLedgerKernel α β) b) =
          2 * Fintype.card I := by
  classical
  have hneI : (univ : Finset I).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ]
    omega
  have hπ2 : ∀ i, 2 ≤ π i := fun i => (hπ i).two_le
  -- By continuity of `weilKernel` at `log(π i) > 0`, for each `i ∈ I` there is `r_i > 0` such that
  -- `0 < t < r_i` implies `α(K(log(π i)) - K(log(π i) - 2t)) + β log(π i)/√(π i) > 0`.
  have hcont : ∀ i : I, ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, 0 < t → t < r →
      0 < α * (RHTower.ArchimedeanKernel.weilKernel (Real.log (π i : ℝ)) -
        RHTower.ArchimedeanKernel.weilKernel (Real.log (π i : ℝ) - 2 * t)) +
      β * (Real.log (π i : ℝ) / Real.sqrt (π i : ℝ)) := by
    intro i
    have hpi1 : (1 : ℝ) < π i := by exact_mod_cast (hπ i).one_lt
    have hlog_pos : 0 < Real.log (π i : ℝ) := Real.log_pos hpi1
    have hcontK : ContinuousAt RHTower.ArchimedeanKernel.weilKernel (Real.log (π i : ℝ)) := by
      unfold RHTower.ArchimedeanKernel.weilKernel
      have hne : 1 - Real.exp (-2 * Real.log (π i : ℝ)) ≠ 0 :=
        (RHTower.ArchimedeanKernel.one_sub_exp_neg_two_mul_pos hlog_pos).ne'
      fun_prop (disch := assumption)
    set g : ℝ → ℝ := fun t =>
      α * (RHTower.ArchimedeanKernel.weilKernel (Real.log (π i : ℝ)) -
        RHTower.ArchimedeanKernel.weilKernel (Real.log (π i : ℝ) - 2 * t)) +
      β * (Real.log (π i : ℝ) / Real.sqrt (π i : ℝ))
    have hg0 : 0 < g 0 := by
      simp only [g, mul_zero, sub_zero, sub_self, zero_add]
      have : 0 < Real.log (π i : ℝ) / Real.sqrt (π i : ℝ) :=
        div_pos hlog_pos (Real.sqrt_pos.2 (by linarith))
      positivity
    have hcg : ContinuousAt g 0 := by
      refine (continuousAt_const.mul (continuousAt_const.sub ?_)).add continuousAt_const
      change ContinuousAt (RHTower.ArchimedeanKernel.weilKernel ∘
        fun t : ℝ => Real.log (π i : ℝ) - 2 * t) 0
      refine ContinuousAt.comp (by simpa using hcontK) ?_
      fun_prop
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (hcg.eventually (lt_mem_nhds hg0))
    refine ⟨r, hr, fun t ht0 htr => hball ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
    exact htr
  choose r hr_pos hr_bound using hcont
  set B : ℕ := univ.sup π + 2
  have hB_ge : ∀ i : I, π i ≤ B := fun i => (le_sup (mem_univ i)).trans (Nat.le_add_right _ 2)
  set ε₁ : ℝ := 1 / (2 * ((B * B : ℕ) : ℝ) + 2)
  have hε₁ : 0 < ε₁ := by positivity
  set ε₀ : ℝ := min ε₁ (univ.inf' hneI r)
  have hε₀ : 0 < ε₀ := lt_min hε₁ ((lt_inf'_iff hneI).2 fun i _ => hr_pos i)
  refine ⟨ε₀, hε₀, fun δ hδ_inj hδ b => ?_⟩
  have hδ0 : ∀ i, 0 < δ i := fun i => (hδ i).1
  have hδ_lt_r : ∀ i, δ i < r i := fun i =>
    (hδ i).2.trans_le ((min_le_right _ _).trans (inf'_le r (mem_univ i)))
  have hδ_prod : ∀ i j, δ i + δ j < 1 / (((π i * π j : ℕ) : ℝ) + 1) := by
    intro i j
    have hi : δ i < ε₁ := (hδ i).2.trans_le (min_le_left _ _)
    have hj : δ j < ε₁ := (hδ j).2.trans_le (min_le_left _ _)
    have hsum : δ i + δ j < 2 * ε₁ := by linarith
    have h2ε₁ : 2 * ε₁ = 1 / (((B * B : ℕ) : ℝ) + 1) := by
      unfold ε₁; field_simp
    rw [h2ε₁] at hsum
    have hle : ((π i * π j : ℕ) : ℝ) + 1 ≤ ((B * B : ℕ) : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul (hB_ge i) (hB_ge j)) 1
    exact hsum.trans_le (one_div_le_one_div_of_le (by positivity) hle)
  have hδ_single : ∀ i, 2 * δ i < 1 / ((π i : ℝ) + 1) := by
    intro i
    have hsum := hδ_prod i i
    have hpi : (2 : ℝ) ≤ π i := by exact_mod_cast hπ2 i
    have hle : ((π i : ℝ) + 1) ≤ ((π i * π i : ℕ) : ℝ) + 1 := by push_cast; nlinarith
    have hinv := one_div_le_one_div_of_le (by positivity) hle
    linarith
  have hcardι : Fintype.card (I × Bool) = Fintype.card I * 2 := by
    rw [Fintype.card_prod, Fintype.card_bool]
  rw [frustrationIndex_oddWeilLedger_of_sparse (collarPos_pos hπ2 hδ0 hδ_single)
    (collarPos_injective hπ2 hδ0 hδ_inj hδ_single) hα hβ.le b (D := 1) (fun x => ?_) (by omega)]
  · have hset : (univ.filter fun q : (I × Bool) × (I × Bool) =>
        q.1 ≠ q.2 ∧ 0 < oddFold (collarPos π δ) (weilLedgerKernel α β) b q.1 q.2) =
        univ.image fun x => (x, collarPartner x) := by
      ext ⟨x, y⟩
      simp only [mem_filter, mem_univ, true_and, mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨hxy, hp⟩
        obtain ⟨n, hn, -⟩ := oddFold_pos_imp_primeSum (collarPos_pos hπ2 hδ0 hδ_single)
          (collarPos_injective hπ2 hδ0 hδ_inj hδ_single) hα.le hβ.le hxy hp
        exact ⟨x, rfl, (eq_collarPartner_of_exp_eq hπ2 hδ0 hδ_inj hδ_prod hxy hn).symm⟩
      · rintro ⟨z, rfl, rfl⟩
        refine ⟨collarPartner_ne z, ?_⟩
        rw [oddFold_collarPartner hπ hδ0 hδ_single]
        exact hr_bound z.1 (δ z.1) (hδ0 z.1) (hδ_lt_r z.1)
    rw [hset, card_image_of_injective _ (fun x y h => (Prod.ext_iff.1 h).1), card_univ, hcardι]
    ring
  · calc (univ.filter (IsPrimeSum (collarPos π δ) x)).card ≤ ({collarPartner x} : Finset _).card := by
          refine card_le_card fun y hy => ?_
          simp only [mem_filter, mem_univ, true_and] at hy
          obtain ⟨hxy, n, hn, -⟩ := hy
          rw [mem_singleton]
          exact eq_collarPartner_of_exp_eq hπ2 hδ0 hδ_inj hδ_prod hxy hn
      _ = 1 := card_singleton _

end Collar

/-- **Multi-layer collar-skimming frustration at full archimedean weight `α = 1, β = 1`**: for any
finite set of primes `Q` and layer count `M ≥ 1` with `2 ≤ M |Q|`, there is an injective sample
`p : (↥Q × Fin M) × Bool → ℝ` in `(0, max_{q ∈ Q} log q]` whose odd Weil ledger at `α = 1, β = 1`
has frustration index `2 M |Q|` (100% of its `2 M |Q|` points frustrated) for every budget `b`. -/
theorem exists_collarPos_frustrationIndex_eq_two_mul {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime)
    (M : ℕ) (hcard : 2 ≤ Q.card * M) :
    ∃ p : (↥Q × Fin M) × Bool → ℝ, Function.Injective p ∧
      (∀ x, 0 < p x ∧ p x ≤ Real.log ((x.1.1 : ℕ) : ℝ)) ∧
      ∀ b : (↥Q × Fin M) × Bool → ℝ,
        frustrationIndex (oddFold p (weilLedgerKernel 1 1) b) = 2 * (Q.card * M) := by
  classical
  let π : ↥Q × Fin M → ℕ := fun x => x.1.1
  have hπ : ∀ i : ↥Q × Fin M, (π i).Prime := fun i => hQ i.1.1 i.1.2
  have hcardI : Fintype.card (↥Q × Fin M) = Q.card * M := by
    rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
  obtain ⟨ε₀, hε₀, hfr⟩ := frustrationIndex_collarPos_fullWeight (I := ↥Q × Fin M) (π := π)
    (by omega) hπ one_pos one_pos
  set B : ℕ := (univ : Finset (↥Q × Fin M)).sup π + 2
  set ε : ℝ := min (ε₀ / 2) (1 / (4 * ((B : ℝ) + 1)))
  have hε : 0 < ε := lt_min (half_pos hε₀) (by positivity)
  have hε_lt : ε < ε₀ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε₀)
  let eqv : ↥Q × Fin M ≃ Fin (Fintype.card (↥Q × Fin M)) := Fintype.equivFin (↥Q × Fin M)
  let δ : ↥Q × Fin M → ℝ := fun i =>
    ε * ((eqv i : ℕ) + 1 : ℝ) / ((Fintype.card (↥Q × Fin M) : ℝ) + 1)
  have hδ0 : ∀ i, 0 < δ i := fun i => by positivity
  have hδ_le : ∀ i, δ i ≤ ε := fun i => by
    have hi_nat : (eqv i : ℕ) + 1 ≤ Fintype.card (↥Q × Fin M) + 1 := by omega
    have hi : ((eqv i : ℕ) + 1 : ℝ) ≤ (Fintype.card (↥Q × Fin M) : ℝ) + 1 := by
      exact_mod_cast hi_nat
    exact div_le_of_le_mul₀ (by positivity) hε.le (mul_le_mul_of_nonneg_left hi hε.le)
  have hδ_inj : Function.Injective δ := fun i₁ i₂ h => by
    have hC : (0 : ℝ) < (Fintype.card (↥Q × Fin M) : ℝ) + 1 := by positivity
    have h1 : ε * ((eqv i₁ : ℕ) + 1 : ℝ) = ε * ((eqv i₂ : ℕ) + 1 : ℝ) :=
      (div_left_inj' hC.ne').1 h
    have h2 : ((eqv i₁ : ℕ) + 1 : ℝ) = ((eqv i₂ : ℕ) + 1 : ℝ) := mul_left_cancel₀ hε.ne' h1
    exact eqv.injective (Fin.ext (by exact_mod_cast add_right_cancel h2))
  have hδ_single : ∀ i, 2 * δ i < 1 / ((π i : ℝ) + 1) := fun i => by
    have h1 : δ i ≤ 1 / (4 * ((B : ℝ) + 1)) := (hδ_le i).trans (min_le_right _ _)
    have hB : (π i : ℝ) ≤ B := by
      exact_mod_cast (le_sup (mem_univ i)).trans (Nat.le_add_right _ 2)
    have hpi : (0 : ℝ) < π i := by exact_mod_cast (hπ i).pos
    have hlt : 1 / (4 * ((B : ℝ) + 1)) < 1 / (2 * ((B : ℝ) + 1)) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    have h2 : 2 * (1 / (4 * ((B : ℝ) + 1))) < 1 / ((B : ℝ) + 1) := by
      have : (B : ℝ) + 1 ≠ 0 := by positivity
      have h_eq : 2 * (1 / (4 * ((B : ℝ) + 1))) = 1 / (2 * ((B : ℝ) + 1)) := by field_simp; ring
      rw [h_eq]
      exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
    have hle : 1 / ((B : ℝ) + 1) ≤ 1 / ((π i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hπ2 : ∀ i, 2 ≤ π i := fun i => (hπ i).two_le
  refine ⟨collarPos π δ, collarPos_injective hπ2 hδ0 hδ_inj hδ_single, fun x => ?_, fun b => ?_⟩
  · refine ⟨collarPos_pos hπ2 hδ0 hδ_single x, ?_⟩
    unfold collarPos
    split_ifs
    · linarith [hδ0 x.1]
    · have h1 := abs_collarPos_sub_partner hπ2 hδ0 hδ_single x
      have h2 := abs_nonneg (collarPos π δ x - collarPos π δ (collarPartner x))
      have h3 := hδ0 x.1
      linarith
  · rw [hfr δ hδ_inj (fun i => ⟨hδ0 i, (hδ_le i).trans_lt hε_lt⟩) b, hcardI]

/-! ### 5. The sub-prime contact regime `A ≤ 3/10` and synthesis with `μ(A)` and `zetaContactAperture` -/

section ContactSynthesis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Below the first prime threshold `½ log 2` (in particular on `(0, 3/10]`), a sample has no
prime-sum pairs. -/
theorem primeSumPairs_eq_empty_of_lt_half_log_two {p : ι → ℝ}
    (hp : ∀ x, p x < Real.log 2 / 2) :
    primeSumPairs p = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  rintro ⟨x, y⟩ hmem
  simp only [primeSumPairs, mem_filter, mem_univ, true_and] at hmem
  obtain ⟨-, n, hn, hΛ⟩ := hmem
  have hn2 : 2 ≤ n := (vonMangoldt_ne_zero_iff.1 hΛ.ne').two_le
  have hsum : p x + p y < Real.log 2 := by linarith [hp x, hp y]
  have hexp : Real.exp (p x + p y) < 2 := by
    calc Real.exp (p x + p y) < Real.exp (Real.log 2) := Real.exp_lt_exp.2 hsum
      _ = 2 := Real.exp_log (by norm_num)
  have hge : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  linarith

/-- On the certified contact window `(0, 3/10]`, every sample has `frustrationIndex = 0`. -/
theorem frustrationIndex_eq_zero_of_le_threeTenths {p : ι → ℝ} (hp0 : ∀ x, 0 < p x)
    (hpA : ∀ x, p x ≤ 3 / 10) (hinj : Function.Injective p) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (b : ι → ℝ) :
    frustrationIndex (oddFold p (weilLedgerKernel α β) b) = 0 := by
  have hlt : ∀ x, p x < Real.log 2 / 2 := fun x => by
    have := hpA x; have := log_two_bounds.1; linarith
  have hle := frustrationIndex_oddWeilLedger_le hp0 hinj hα hβ b
  rw [primeSumPairs_eq_empty_of_lt_half_log_two hlt, card_empty] at hle
  omega

/-- On the certified contact window `(0, 3/10]`, every sample has `frustrationMass = 0`. -/
theorem frustrationMass_eq_zero_of_le_threeTenths {p : ι → ℝ} (hp0 : ∀ x, 0 < p x)
    (hpA : ∀ x, p x ≤ 3 / 10) (hinj : Function.Injective p) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (b : ι → ℝ) :
    frustrationMass (oddFold p (weilLedgerKernel α β) b) = 0 := by
  have hlt : ∀ x, p x < Real.log 2 / 2 := fun x => by
    have := hpA x; have := log_two_bounds.1; linarith
  have hle := frustrationMass_oddWeilLedger_le hp0 hinj hα hβ b
  rw [primeSumPairs_eq_empty_of_lt_half_log_two hlt, sum_empty] at hle
  exact le_antisymm hle (frustrationMass_nonneg _)

/-- **Master Synthesis of Off-Lattice Frustration, Full-Weight Calibration, and the Contact
Aperture.**
Unites the five regimes of Open Problem 1:
1. **Sub-prime contact regime `(0, 3/10]`**: every sample has `frustrationIndex = 0` and
   `frustrationMass = 0`, the restricted Weil ground energy satisfies `μ(A) ≥ 1/5000`, and off RH
   `3/10 ≤ zetaContactAperture`;
2. **Midpoint quenching at full weight `α = 1, β = 1`**: the polar barrier `-8 sinh(p_x/2) sinh(p_y/2)`
   quenches the midpoint-matched family `matchedPos Q` (`q ≥ 5`) to `frustrationIndex = 0` and
   `frustrationMass = 0`;
3. **Source-faithful prime triangle (`Fin 3`) and packed prime configuration (`Fin 4`) at full
   weight `α = 1, β = 1`**: `primeTrianglePos` has `frustrationIndex = 2` and
   `frustrationMass ∈ (2/7, 4/5)` for every budget `b`, `packedPrimePos` has `misalignedCount 1 = 4`
   reduced by switching vertex `1` to `frustrationIndex = 2` and `frustrationMass < 4/5`, and both
   are paid along canonical paths (`0 ≤ incidenceEnergy`);
4. **Dense multi-triangle packing at full weight `α = 1, β = 1`**: for every `M ≥ 1` there are
   `3M`-point samples in `(0, log 5]` with `frustrationIndex ≥ 2M` and `frustrationMass ≥ (2/7) M`;
5. **Collar-skimming survival at full weight `α = 1, β = 1`**: for every finite set of primes `Q`
   and layer count `M ≥ 1` (`2 ≤ M |Q|`), there are `2 M |Q|`-point samples in
   `(0, max_{q ∈ Q} log q]` with `frustrationIndex = 2 M |Q|`. -/
theorem oddWeilLedger_offLattice_frustration_and_contact_synthesis :
    (∀ (p : ι → ℝ), (∀ x, 0 < p x) → (∀ x, p x ≤ 3 / 10) → Function.Injective p →
      ∀ b : ι → ℝ,
        frustrationIndex (oddFold p (weilLedgerKernel 1 1) b) = 0 ∧
        frustrationMass (oddFold p (weilLedgerKernel 1 1) b) = 0) ∧
    (∀ A : SuzukiPositiveAperture, A.1 ≤ 3 / 10 → 1 / 5000 ≤ ccmRestrictedWeilGroundEnergy A) ∧
    (¬ RiemannHypothesis → (3 / 10 : ℝ) ≤ zetaContactAperture) ∧
    (∀ (Q : Finset ℕ), (∀ q ∈ Q, q.Prime ∧ 5 ≤ q) → ∀ b : ↥Q × Bool → ℝ,
      frustrationIndex (oddFold (matchedPos Q) (weilLedgerKernel 1 1) b) = 0 ∧
      frustrationMass (oddFold (matchedPos Q) (weilLedgerKernel 1 1) b) = 0) ∧
    (∀ b : Fin 3 → ℝ,
      frustrationIndex (oddFold primeTrianglePos (weilLedgerKernel 1 1) b) = 2 ∧
      (2 / 7 : ℝ) ≤ frustrationMass (oddFold primeTrianglePos (weilLedgerKernel 1 1) b) ∧
      frustrationMass (oddFold primeTrianglePos (weilLedgerKernel 1 1) b) < 4 / 5) ∧
    (∀ b : Fin 4 → ℝ,
      misalignedCount (fun _ => 1) (oddFold packedPrimePos (weilLedgerKernel 1 1) b) = 4 ∧
      frustrationIndex (oddFold packedPrimePos (weilLedgerKernel 1 1) b) = 2 ∧
      frustrationMass (oddFold packedPrimePos (weilLedgerKernel 1 1) b) < 4 / 5) ∧
    (∀ f : Fin 3 → ℝ,
      0 ≤ incidenceEnergy
        (oddFold primeTrianglePos (weilLedgerKernel 1 1) primeTriangleCanonicalBudget) f) ∧
    (∀ f : Fin 4 → ℝ,
      0 ≤ incidenceEnergy
        (oddFold packedPrimePos (weilLedgerKernel 1 1) packedPrimeCanonicalBudget) f) ∧
    (∀ M : ℕ, ∃ p : Fin M × Fin 3 → ℝ, Function.Injective p ∧
      (∀ x, 0 < p x ∧ p x ≤ Real.log 5) ∧
      ∀ b : Fin M × Fin 3 → ℝ,
        2 * M ≤ frustrationIndex (oddFold p (weilLedgerKernel 1 1) b) ∧
          (2 / 7 : ℝ) * M ≤ frustrationMass (oddFold p (weilLedgerKernel 1 1) b)) ∧
    (∀ (Q : Finset ℕ), (∀ q ∈ Q, q.Prime) → ∀ M : ℕ, 2 ≤ Q.card * M →
      ∃ p : (↥Q × Fin M) × Bool → ℝ, Function.Injective p ∧
        (∀ x, 0 < p x ∧ p x ≤ Real.log ((x.1.1 : ℕ) : ℝ)) ∧
        ∀ b : (↥Q × Fin M) × Bool → ℝ,
          frustrationIndex (oddFold p (weilLedgerKernel 1 1) b) = 2 * (Q.card * M)) :=
  ⟨fun _ hp0 hpA hinj b =>
      ⟨frustrationIndex_eq_zero_of_le_threeTenths hp0 hpA hinj zero_le_one zero_le_one b,
       frustrationMass_eq_zero_of_le_threeTenths hp0 hpA hinj zero_le_one zero_le_one b⟩,
   fun _ hA => one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeTenths hA,
   threeTenths_le_zetaContactAperture,
   fun _ hQ b =>
      ⟨frustrationIndex_matchedPos_weilLedgerKernel_one_eq_zero hQ b,
       frustrationMass_matchedPos_weilLedgerKernel_one_eq_zero hQ b⟩,
   fun b =>
      ⟨frustrationIndex_primeTriangle_weilLedgerKernel_one b,
       (frustrationMass_primeTriangle_weilLedgerKernel_one_bounds b).1,
       (frustrationMass_primeTriangle_weilLedgerKernel_one_bounds b).2⟩,
   fun b =>
      ⟨(frustrationIndex_packedPrime_weilLedgerKernel_one b).1,
       (frustrationIndex_packedPrime_weilLedgerKernel_one b).2,
       (frustrationMass_packedPrime_weilLedgerKernel_one_lt b).1⟩,
   incidenceEnergy_oddFold_primeTriangleCanonical_nonneg,
   incidenceEnergy_oddFold_packedPrimeCanonical_nonneg,
   exists_dense_primeTriangle_packing_weilLedgerKernel_one,
   fun _ hQ M hM => exists_collarPos_frustrationIndex_eq_two_mul hQ M hM⟩

end ContactSynthesis

end

end GaloisForLFunctions.ArithmeticOrientationTheory
