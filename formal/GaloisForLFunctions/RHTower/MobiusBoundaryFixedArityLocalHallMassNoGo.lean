import GaloisForLFunctions.RHTower.MobiusBoundaryOppositeSignTransport
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount
import GaloisForLFunctions.HTGeometry.FactorialCompositionBound
import GaloisForLFunctions.PNTPlus.Mathlib.NumberTheory.Sieve.SelbergBounds

/-!
# Fixed-arity local Hall mass obstruction for Route E

For every fixed replacement arity `k`, products of `12 * (k + 1)` distinct primes
in `(Y, 2Y]` form a near-linear family of squarefree source vertices.  At boundary
`N = (2Y)^(12*(k+1))`, all common-spectator replacements using at most `k` source
prime factors move these vertices by more than `H = (2Y)^(8*(k+1)) = N^(2/3)`.
Consequently their isolated Gibbs mass eventually exceeds every constant multiple
of `H`.  This rules out every fixed-arity, common-spectator, `N^(2/3)`-local
positive-defect Hall/fractional-transport implementation; half-power-local versions
are a fortiori impossible.
-/

open scoped BigOperators
open Filter

namespace RHTower

noncomputable section

/-- One endpoint is obtained by replacing a token of at most `k` source primes while retaining a
common multiplicative spectator. -/
def RouteEBoundedAritySpectatorReplacement (k n m : ℕ) : Prop :=
  ∃ a v : ℕ, ∃ T : Finset ℕ,
    T.card ≤ k ∧
    (∀ p ∈ T, p.Prime) ∧
    n = (∏ p ∈ T, p) * a ∧
    m = v * a ∧
    (∏ p ∈ T, p) ≠ v

theorem le_pow_mul_dist_of_boundedAritySpectatorReplacement_of_primeFactors_le
    {y k n m : ℕ} (hy : 1 ≤ y)
    (hn : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ y)
    (hrep : RouteEBoundedAritySpectatorReplacement k n m) :
    n ≤ y ^ k * Nat.dist n m := by
  obtain ⟨a, v, T, hTk, hTprime, hnT, hmv, hne⟩ := hrep
  let u := ∏ p ∈ T, p
  have hpy : ∀ p ∈ T, p ≤ y := by
    intro p hp
    apply hn p (hTprime p hp)
    rw [hnT]
    exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem (fun q => q) hp) a
  have hu : u ≤ y ^ k := by
    calc
      u ≤ ∏ _p ∈ T, y := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hpy
      _ = y ^ T.card := by simp
      _ ≤ y ^ k := Nat.pow_le_pow_right hy hTk
  rw [hnT, hmv]
  rw [Nat.dist_mul_right]
  have hdist : 1 ≤ Nat.dist u v := Nat.dist_pos_of_ne hne
  calc
    u * a ≤ y ^ k * a := Nat.mul_le_mul_right a hu
    _ ≤ y ^ k * (Nat.dist u v * a) := by
      apply Nat.mul_le_mul_left
      simpa using Nat.mul_le_mul_right a hdist

open GaloisForLFunctions.HTGeometry

/-- Products of exactly `r` distinct primes in the multiplicative window `(Y,2Y]`. -/
def routeEFixedDepthPrimeProducts (Y r : ℕ) : Finset ℕ :=
  (primesInIoc Y (2 * Y)).powersetCard r |>.image fun T => ∏ p ∈ T, p

theorem card_routeEFixedDepthPrimeProducts (Y r : ℕ) :
    (routeEFixedDepthPrimeProducts Y r).card =
      (primesInIoc Y (2 * Y)).card.choose r := by
  classical
  rw [routeEFixedDepthPrimeProducts, Finset.card_image_iff.mpr]
  · exact Finset.card_powersetCard r _
  · intro S hS T hT hprod
    have hSprime : ∀ p ∈ S, p.Prime := fun p hp =>
      (mem_primesInIoc ((Finset.mem_powersetCard.mp hS).1 hp)).1
    have hTprime : ∀ p ∈ T, p.Prime := fun p hp =>
      (mem_primesInIoc ((Finset.mem_powersetCard.mp hT).1 hp)).1
    calc
      S = (∏ p ∈ S, p).primeFactors := (Nat.primeFactors_prod hSprime).symm
      _ = (∏ p ∈ T, p).primeFactors := congrArg Nat.primeFactors hprod
      _ = T := Nat.primeFactors_prod hTprime

theorem routeEFixedDepthPrimeProducts_squarefree
    {Y r n : ℕ} (hn : n ∈ routeEFixedDepthPrimeProducts Y r) :
    Squarefree n := by
  classical
  rw [routeEFixedDepthPrimeProducts, Finset.mem_image] at hn
  obtain ⟨T, hT, rfl⟩ := hn
  exact _root_.Sieve.prodDistinctPrimes_squarefree T fun p hp =>
    (mem_primesInIoc ((Finset.mem_powersetCard.mp hT).1 hp)).1

theorem primeFactors_le_two_mul_of_mem_routeEFixedDepthPrimeProducts
    {Y r n : ℕ} (hn : n ∈ routeEFixedDepthPrimeProducts Y r) :
    ∀ p : ℕ, p.Prime → p ∣ n → p ≤ 2 * Y := by
  classical
  rw [routeEFixedDepthPrimeProducts, Finset.mem_image] at hn
  obtain ⟨T, hT, rfl⟩ := hn
  intro p hp hpdvd
  have hP : ∀ q ∈ primesInIoc Y (2 * Y), q.Prime := fun q hq => (mem_primesInIoc hq).1
  have hsub := (Finset.mem_powersetCard.mp hT).1
  have hpf := Nat.primeFactors_prod (fun p hp => hP p (hsub hp))
  have hpmem : p ∈ (∏ q ∈ T, q).primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨hp, hpdvd, ?_⟩
    exact Finset.prod_ne_zero_iff.mpr fun q hq =>
      ((hP q (hsub hq)).pos.ne')
  rw [hpf] at hpmem
  exact (mem_primesInIoc (hsub hpmem)).2.2

theorem routeEFixedDepthPrimeProducts_le
    {Y r n : ℕ} (hn : n ∈ routeEFixedDepthPrimeProducts Y r) :
    n ≤ (2 * Y) ^ r := by
  classical
  rw [routeEFixedDepthPrimeProducts, Finset.mem_image] at hn
  obtain ⟨T, hT, rfl⟩ := hn
  have hcard := (Finset.mem_powersetCard.mp hT).2
  calc
    (∏ p ∈ T, p) ≤ ∏ _p ∈ T, (2 * Y) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact Nat.zero_le _
      · intro p hp
        exact (mem_primesInIoc ((Finset.mem_powersetCard.mp hT).1 hp)).2.2
    _ = (2 * Y) ^ T.card := by simp
    _ = (2 * Y) ^ r := by rw [hcard]

theorem pow_lt_routeEFixedDepthPrimeProducts
    {Y r n : ℕ} (hY : 0 < Y) (hr : 0 < r)
    (hn : n ∈ routeEFixedDepthPrimeProducts Y r) :
    Y ^ r < n := by
  classical
  rw [routeEFixedDepthPrimeProducts, Finset.mem_image] at hn
  obtain ⟨T, hT, rfl⟩ := hn
  have hcard := (Finset.mem_powersetCard.mp hT).2
  have hTnon : T.Nonempty := Finset.card_pos.mp (hcard.trans_gt hr)
  obtain ⟨p, hpT⟩ := hTnon
  calc
    Y ^ r = ∏ _q ∈ T, Y := by simp [hcard]
    _ < ∏ q ∈ T, q := by
      apply Finset.prod_lt_prod
      · intro q hq
        exact hY
      · intro q hq
        exact (mem_primesInIoc ((Finset.mem_powersetCard.mp hT).1 hq)).2.1.le
      · exact ⟨p, hpT,
          (mem_primesInIoc ((Finset.mem_powersetCard.mp hT).1 hpT)).2.1⟩

/-- A local fixed-arity spectator-replacement edge. -/
def RouteEBoundedArityWindowAdjacent (k H n m : ℕ) : Prop :=
  RouteEBoundedAritySpectatorReplacement k n m ∧ Nat.dist n m ≤ H

/-- Every depth-`r` product in one prime window is isolated once its forced multiplicative gap
exceeds the permitted displacement. -/
theorem not_boundedArityWindowAdjacent_of_mem_fixedDepthPrimeProducts
    {Y r k H n m : ℕ} (hY : 0 < Y) (hr : 0 < r)
    (hscale : (2 * Y) ^ k * H < Y ^ r)
    (hn : n ∈ routeEFixedDepthPrimeProducts Y r) :
    ¬ RouteEBoundedArityWindowAdjacent k H n m := by
  intro h
  have hgap :=
    le_pow_mul_dist_of_boundedAritySpectatorReplacement_of_primeFactors_le
      (y := 2 * Y) (k := k) (n := n) (m := m) (by omega)
      (primeFactors_le_two_mul_of_mem_routeEFixedDepthPrimeProducts hn) h.1
  have hupper : (2 * Y) ^ k * Nat.dist n m ≤ (2 * Y) ^ k * H :=
    Nat.mul_le_mul_left _ h.2
  have hlower := pow_lt_routeEFixedDepthPrimeProducts hY hr hn
  omega

abbrev RouteEFiniteNatVertex (N : ℕ) := Fin (N + 1)

def routeEBoundedArityWindowAdjacentOn (k H N : ℕ)
    (n m : RouteEFiniteNatVertex N) : Prop :=
  RouteEBoundedArityWindowAdjacent k H n m

noncomputable def routeEFiniteIsolatedGibbsMass (k H N : ℕ) : ℝ := by
  letI := Classical.decRel (routeEBoundedArityWindowAdjacentOn k H N)
  exact ∑ n : RouteEFiniteNatVertex N,
    finiteIsolatedResidual (routeEBoundedArityWindowAdjacentOn k H N)
      (fun m => Real.exp (-((m : ℝ) / (N : ℝ)))) n

def routeEFixedDepthPrimeProductVertex
    (Y r : ℕ) (n : {n // n ∈ routeEFixedDepthPrimeProducts Y r}) :
    RouteEFiniteNatVertex ((2 * Y) ^ r) :=
  ⟨n, Nat.lt_succ_of_le (routeEFixedDepthPrimeProducts_le n.property)⟩

theorem routeEFixedDepthPrimeProductVertex_injective (Y r : ℕ) :
    Function.Injective (routeEFixedDepthPrimeProductVertex Y r) := by
  intro n m h
  apply Subtype.ext
  exact Fin.ext_iff.mp h

theorem finiteReplacementDegree_fixedDepthPrimeProductVertex_eq_zero
    {Y r k H : ℕ} (hY : 0 < Y) (hr : 0 < r)
    (hscale : (2 * Y) ^ k * H < Y ^ r)
    (n : {n // n ∈ routeEFixedDepthPrimeProducts Y r}) :
    letI := Classical.decRel
      (routeEBoundedArityWindowAdjacentOn k H ((2 * Y) ^ r))
    finiteReplacementDegree
      (routeEBoundedArityWindowAdjacentOn k H ((2 * Y) ^ r))
      (routeEFixedDepthPrimeProductVertex Y r n) = 0 := by
  classical
  rw [finiteReplacementDegree, Finset.card_eq_zero]
  by_contra hne
  obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  rw [finiteReplacementNeighbors, Finset.mem_filter] at hm
  exact not_boundedArityWindowAdjacent_of_mem_fixedDepthPrimeProducts
    hY hr hscale n.property hm.2

theorem routeEFixedDepthPrimeProduct_exp_neg_one_le
    {Y r : ℕ} (hY : 0 < Y)
    (n : {n // n ∈ routeEFixedDepthPrimeProducts Y r}) :
    Real.exp (-1) ≤
      Real.exp (-((((routeEFixedDepthPrimeProductVertex Y r n : ℕ) : ℝ) /
        (((2 * Y) ^ r : ℕ) : ℝ)))) := by
  rw [Real.exp_le_exp]
  have hNpos : (0 : ℝ) < (((2 * Y) ^ r : ℕ) : ℝ) := by positivity
  have hnle : ((n.1 : ℕ) : ℝ) ≤ (((2 * Y) ^ r : ℕ) : ℝ) := by
    exact_mod_cast routeEFixedDepthPrimeProducts_le n.property
  simp only [routeEFixedDepthPrimeProductVertex]
  change -1 ≤ -((n.1 : ℝ) / (((2 * Y) ^ r : ℕ) : ℝ))
  rw [neg_le_neg_iff, div_le_one hNpos]
  exact hnle

/-- Exact finite mass obstruction: every fixed-depth prime product is isolated, so the positive
unused-capacity defect is at least its cardinality times `e⁻¹`. -/
theorem card_mul_exp_neg_one_le_routeEFiniteIsolatedGibbsMass
    {Y r k H : ℕ} (hY : 0 < Y) (hr : 0 < r)
    (hscale : (2 * Y) ^ k * H < Y ^ r) :
    ((routeEFixedDepthPrimeProducts Y r).card : ℝ) * Real.exp (-1) ≤
      routeEFiniteIsolatedGibbsMass k H ((2 * Y) ^ r) := by
  classical
  let selected : Finset (RouteEFiniteNatVertex ((2 * Y) ^ r)) :=
    Finset.univ.image (routeEFixedDepthPrimeProductVertex Y r)
  have hselected : selected.card = (routeEFixedDepthPrimeProducts Y r).card := by
    dsimp [selected]
    rw [Finset.card_image_of_injective _
      (routeEFixedDepthPrimeProductVertex_injective Y r)]
    simp
  have hpoint : ∀ n : {n // n ∈ routeEFixedDepthPrimeProducts Y r},
      Real.exp (-1) ≤
        finiteIsolatedResidual
          (routeEBoundedArityWindowAdjacentOn k H ((2 * Y) ^ r))
          (fun m => Real.exp (-((m : ℝ) / (((2 * Y) ^ r : ℕ) : ℝ))))
          (routeEFixedDepthPrimeProductVertex Y r n) := by
    intro n
    rw [finiteIsolatedResidual,
      if_pos (finiteReplacementDegree_fixedDepthPrimeProductVertex_eq_zero
        hY hr hscale n)]
    exact routeEFixedDepthPrimeProduct_exp_neg_one_le hY n
  calc
    ((routeEFixedDepthPrimeProducts Y r).card : ℝ) * Real.exp (-1) =
        ∑ n : {n // n ∈ routeEFixedDepthPrimeProducts Y r}, Real.exp (-1) := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ n : {n // n ∈ routeEFixedDepthPrimeProducts Y r},
        finiteIsolatedResidual
          (routeEBoundedArityWindowAdjacentOn k H ((2 * Y) ^ r))
          (fun m => Real.exp (-((m : ℝ) / (((2 * Y) ^ r : ℕ) : ℝ))))
          (routeEFixedDepthPrimeProductVertex Y r n) :=
      Finset.sum_le_sum fun n _hn => hpoint n
    _ = ∑ n ∈ selected,
        finiteIsolatedResidual
          (routeEBoundedArityWindowAdjacentOn k H ((2 * Y) ^ r))
          (fun m => Real.exp (-((m : ℝ) / (((2 * Y) ^ r : ℕ) : ℝ)))) n := by
      dsimp [selected]
      symm
      apply Finset.sum_image
      intro a _ha b _hb hab
      exact routeEFixedDepthPrimeProductVertex_injective Y r hab
    _ ≤ routeEFiniteIsolatedGibbsMass k H ((2 * Y) ^ r) := by
      rw [routeEFiniteIsolatedGibbsMass]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ selected)
      intro n _hn _hnot
      rw [finiteIsolatedResidual]
      split_ifs
      · exact (Real.exp_pos _).le
      · exact le_rfl

theorem eventually_cube_le_card_primesInIoc_pow_four :
    ∀ᶠ Y : ℕ in atTop,
      (Y : ℝ) ^ 3 ≤ ((primesInIoc Y (2 * Y)).card : ℝ) ^ 4 := by
  have hpntReal := eventually_primeCount_window_ge (K := (2 : ℝ)) (by norm_num)
  have hpntNat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hpntReal
  have hlogReal :=
    (isLittleO_log_rpow_atTop (r := (1 / 4 : ℝ)) (by norm_num)).bound
      (c := (1 / 4 : ℝ)) (by norm_num)
  have hlogNat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hlogReal
  filter_upwards [hpntNat, hlogNat, eventually_ge_atTop 2] with Y hpnt hlog hY
  have hYr : (0 : ℝ) < Y := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hY)
  have hlogY : (0 : ℝ) < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast hY)
  have hpnt' : (Y : ℝ) / (2 * Real.log (Y : ℝ)) ≤
      ((primesInIoc Y (2 * Y)).card : ℝ) := by
    have hfloorTwo : ⌊(2 : ℝ) * (Y : ℝ)⌋₊ = 2 * Y := by
      rw [show (2 : ℝ) * (Y : ℝ) = ((2 * Y : ℕ) : ℝ) by norm_num,
        Nat.floor_natCast]
    have hfloorOne : ⌊(Y : ℝ)⌋₊ = Y := by norm_num
    rw [hfloorTwo, hfloorOne] at hpnt
    rw [card_primesInIoc (by omega)]
    convert hpnt using 1 <;> ring
  have hquarter : 4 * Real.log (Y : ℝ) ≤ (Y : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hlogY, abs_of_nonneg (Real.rpow_nonneg hYr.le _)] at hlog
    nlinarith
  let M : ℝ := ((primesInIoc Y (2 * Y)).card : ℝ)
  let q : ℝ := (Y : ℝ) ^ (1 / 4 : ℝ)
  have hM : 0 ≤ M := by positivity
  have hq : 0 ≤ q := Real.rpow_nonneg hYr.le _
  have hYM : (Y : ℝ) ≤ M * q := by
    have hdiv : (Y : ℝ) ≤ M * (2 * Real.log (Y : ℝ)) := by
      rw [← div_le_iff₀ (by positivity)]
      simpa [M, mul_comm, mul_left_comm, mul_assoc] using hpnt'
    exact hdiv.trans (mul_le_mul_of_nonneg_left (by linarith [hquarter]) hM)
  have hpow := pow_le_pow_left₀ hYr.le hYM 4
  have hqpow : q ^ 4 = (Y : ℝ) := by
    dsimp [q]
    convert Real.rpow_inv_natCast_pow hYr.le (show (4 : ℕ) ≠ 0 by norm_num) using 1 <;>
      norm_num
  have hmul : (Y : ℝ) ^ 4 ≤ M ^ 4 * (Y : ℝ) := by
    calc
      (Y : ℝ) ^ 4 ≤ (M * q) ^ 4 := hpow
      _ = M ^ 4 * q ^ 4 := by rw [mul_pow]
      _ = M ^ 4 * (Y : ℝ) := by rw [hqpow]
  have hcancel : (Y : ℝ) ^ 3 ≤ M ^ 4 := by
    have hYpow : (Y : ℝ) ^ 4 = (Y : ℝ) ^ 3 * (Y : ℝ) := by ring
    rw [hYpow] at hmul
    exact le_of_mul_le_mul_right (by simpa [mul_comm] using hmul) hYr
  exact hcancel

theorem eventually_cube_le_card_primesInIoc_pow_four_nat :
    ∀ᶠ Y : ℕ in atTop,
      Y ^ 3 ≤ (primesInIoc Y (2 * Y)).card ^ 4 := by
  filter_upwards [eventually_cube_le_card_primesInIoc_pow_four] with Y hY
  exact_mod_cast hY

theorem eventually_fixedDepthPrimeProducts_card_lower (k : ℕ) :
    ∀ᶠ Y : ℕ in atTop,
      Y ^ (9 * (k + 1)) ≤
        (2 ^ (12 * (k + 1)) * (12 * (k + 1)).factorial) *
          (routeEFixedDepthPrimeProducts Y (12 * (k + 1))).card := by
  let a := k + 1
  let r := 12 * a
  filter_upwards [eventually_cube_le_card_primesInIoc_pow_four_nat,
    eventually_ge_atTop (((2 * r) ^ 4) + 1)] with Y hcube hY
  let M := (primesInIoc Y (2 * Y)).card
  have ha : 0 < a := by omega
  have hr : 0 < r := by omega
  have hMr : 2 * r ≤ M := by
    by_contra hnot
    have hMlt : M < 2 * r := Nat.lt_of_not_ge hnot
    have hpowlt : M ^ 4 < (2 * r) ^ 4 := Nat.pow_lt_pow_left hMlt (by norm_num)
    have hconst : (2 * r) ^ 4 < Y ^ 3 := by
      have hYpos : 1 ≤ Y := by omega
      exact lt_of_lt_of_le (by omega) (le_self_pow hYpos (by norm_num))
    have hcubeM : Y ^ 3 ≤ M ^ 4 := by simpa [M] using hcube
    exact (not_lt_of_ge hcubeM) (hpowlt.trans hconst)
  have hchoose :=
    GaloisForLFunctions.HTGeometry.pow_le_two_pow_mul_factorial_mul_choose hMr
  have hraise := pow_le_pow_left' hcube (3 * a)
  have hlower : Y ^ (9 * a) ≤ M ^ r := by
    dsimp [M, r] at hraise ⊢
    rw [← pow_mul, ← pow_mul] at hraise
    convert hraise using 1 <;> congr 1 <;> omega
  rw [card_routeEFixedDepthPrimeProducts]
  dsimp [M, r, a] at hchoose ⊢
  exact hlower.trans (by simpa [mul_assoc] using hchoose)

theorem eventually_fixedArity_scale_separates (k : ℕ) :
    ∀ᶠ Y : ℕ in atTop,
      (2 * Y) ^ k * (2 * Y) ^ (8 * (k + 1)) < Y ^ (12 * (k + 1)) := by
  filter_upwards [eventually_ge_atTop (2 ^ (9 * k + 8) + 1)] with Y hY
  have hpowpos : 0 < 2 ^ (9 * k + 8) := pow_pos (by omega) _
  have hYpos : 0 < Y := by omega
  have hconst : 2 ^ (9 * k + 8) < Y ^ (3 * k + 4) := by
    have hbase : 2 ^ (9 * k + 8) < Y := by omega
    exact hbase.trans_le (le_self_pow (by omega) (by omega))
  calc
    (2 * Y) ^ k * (2 * Y) ^ (8 * (k + 1)) =
        (2 * Y) ^ (9 * k + 8) := by rw [← pow_add]; congr 1 <;> omega
    _ = 2 ^ (9 * k + 8) * Y ^ (9 * k + 8) := by rw [mul_pow]
    _ < Y ^ (3 * k + 4) * Y ^ (9 * k + 8) :=
      Nat.mul_lt_mul_of_pos_right hconst (pow_pos hYpos _)
    _ = Y ^ (12 * (k + 1)) := by rw [← pow_add]; congr 1 <;> omega

/-- The isolated positive defect beats every constant multiple of the broad `N^(2/3)` envelope.
This is much larger than the `N^(1/2+o(1))` envelope needed by Route E. -/
theorem eventually_const_mul_twoThirdScale_lt_routeEFiniteIsolatedGibbsMass
    (k : ℕ) (C : ℝ) :
    ∀ᶠ Y : ℕ in atTop,
      C * (((2 * Y) ^ (8 * (k + 1)) : ℕ) : ℝ) <
        routeEFiniteIsolatedGibbsMass k ((2 * Y) ^ (8 * (k + 1)))
          ((2 * Y) ^ (12 * (k + 1))) := by
  let a := k + 1
  let r := 12 * a
  let h := 8 * a
  let D : ℕ := 2 ^ r * r.factorial
  let Cpos : ℝ := max C 0
  let K : ℝ := Cpos * (2 : ℝ) ^ h * (D : ℝ) * Real.exp 1
  have ha : 0 < a := by omega
  have hr : 0 < r := by omega
  have hDposNat : 0 < D := by
    dsimp [D]
    exact Nat.mul_pos (pow_pos (by omega) _) (Nat.factorial_pos _)
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hDposNat
  have hKbase : ∀ᶠ Y : ℕ in atTop, K < (Y : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_gt_atTop K)
  have hK : ∀ᶠ Y : ℕ in atTop, K < (Y : ℝ) ^ a := by
    filter_upwards [hKbase, eventually_ge_atTop 1] with Y hKY hY
    have hnat : Y ≤ Y ^ a := le_self_pow hY ha.ne'
    have hreal : (Y : ℝ) ≤ (Y : ℝ) ^ a := by exact_mod_cast hnat
    exact hKY.trans_le hreal
  filter_upwards [eventually_fixedDepthPrimeProducts_card_lower k,
    eventually_fixedArity_scale_separates k, hK,
    eventually_ge_atTop 1] with Y hcard hscale hKY hY
  have hYposNat : 0 < Y := by omega
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hYposNat
  have hcardReal : (Y : ℝ) ^ (9 * a) ≤
      (D : ℝ) * ((routeEFixedDepthPrimeProducts Y r).card : ℝ) := by
    dsimp [a, r, D] at hcard ⊢
    exact_mod_cast hcard
  have hmass := card_mul_exp_neg_one_le_routeEFiniteIsolatedGibbsMass
    hYposNat hr (by simpa [r, h, a] using hscale)
  have hcoef :
      Cpos * (2 : ℝ) ^ h * (D : ℝ) * Real.exp 1 < (Y : ℝ) ^ a := by
    simpa [K] using hKY
  have hcoefMul :
      (Cpos * (2 : ℝ) ^ h * (D : ℝ) * Real.exp 1) * (Y : ℝ) ^ h <
        (Y : ℝ) ^ (9 * a) := by
    have hmul := mul_lt_mul_of_pos_right hcoef (pow_pos hYpos h)
    calc
      (Cpos * (2 : ℝ) ^ h * (D : ℝ) * Real.exp 1) * (Y : ℝ) ^ h <
          (Y : ℝ) ^ a * (Y : ℝ) ^ h := hmul
      _ = (Y : ℝ) ^ (9 * a) := by
        rw [← pow_add]
        congr 1
        dsimp [h]
        omega
  have hexp : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hscaled :
      (Cpos * (((2 * Y) ^ h : ℕ) : ℝ)) * ((D : ℝ) * Real.exp 1) <
        (((routeEFixedDepthPrimeProducts Y r).card : ℝ) * Real.exp (-1)) *
          ((D : ℝ) * Real.exp 1) := by
    calc
      (Cpos * (((2 * Y) ^ h : ℕ) : ℝ)) * ((D : ℝ) * Real.exp 1) =
          (Cpos * (2 : ℝ) ^ h * (D : ℝ) * Real.exp 1) * (Y : ℝ) ^ h := by
        push_cast
        rw [mul_pow]
        ring
      _ < (Y : ℝ) ^ (9 * a) := hcoefMul
      _ ≤ (D : ℝ) * ((routeEFixedDepthPrimeProducts Y r).card : ℝ) := hcardReal
      _ = (((routeEFixedDepthPrimeProducts Y r).card : ℝ) * Real.exp (-1)) *
          ((D : ℝ) * Real.exp 1) := by
        symm
        calc
          (((routeEFixedDepthPrimeProducts Y r).card : ℝ) * Real.exp (-1)) *
              ((D : ℝ) * Real.exp 1) =
              (D : ℝ) * ((routeEFixedDepthPrimeProducts Y r).card : ℝ) *
                (Real.exp (-1) * Real.exp 1) := by ring
          _ = (D : ℝ) * ((routeEFixedDepthPrimeProducts Y r).card : ℝ) := by
            rw [hexp, mul_one]
  have hpositive : 0 ≤ (D : ℝ) * Real.exp 1 := by positivity
  have hcore : Cpos * (((2 * Y) ^ h : ℕ) : ℝ) <
      ((routeEFixedDepthPrimeProducts Y r).card : ℝ) * Real.exp (-1) :=
    lt_of_mul_lt_mul_right hscaled hpositive
  have hCpos : C ≤ Cpos := le_max_left _ _
  have hscaleNonneg : 0 ≤ (((2 * Y) ^ h : ℕ) : ℝ) := by positivity
  have hCcore : C * (((2 * Y) ^ h : ℕ) : ℝ) <
      ((routeEFixedDepthPrimeProducts Y r).card : ℝ) * Real.exp (-1) :=
    (mul_le_mul_of_nonneg_right hCpos hscaleNonneg).trans_lt hcore
  exact hCcore.trans_le (by simpa [r, h, a] using hmass)

/-- Candidate class in which a fixed-arity spectator-preserving local Hall graph has isolated
positive defect bounded at the broad `N^(2/3)` scale.  Any `N^(1/2+o(1))` Route E Hall producer
would satisfy this necessary bound by taking exponent `1/2 + 1/6`. -/
def RouteEFixedArityTwoThirdLocalHallDefectRoute : Prop :=
  ∃ k : ℕ, ∃ C : ℝ,
    ∀ᶠ Y : ℕ in atTop,
      routeEFiniteIsolatedGibbsMass k ((2 * Y) ^ (8 * (k + 1)))
          ((2 * Y) ^ (12 * (k + 1))) ≤
        C * (((2 * Y) ^ (8 * (k + 1)) : ℕ) : ℝ)

/-- Premise-free Route E class kill: no fixed-arity common-spectator replacement graph with
half-power-local displacement can have a half-power-sized positive Hall defect. -/
theorem routeEFixedArityTwoThirdLocalHallDefectRouteKilled :
    ¬ RouteEFixedArityTwoThirdLocalHallDefectRoute := by
  rintro ⟨k, C, hbound⟩
  have hlower :=
    eventually_const_mul_twoThirdScale_lt_routeEFiniteIsolatedGibbsMass k C
  obtain ⟨Y, hupper, hlowerY⟩ := (hbound.and hlower).exists
  exact (not_lt_of_ge hupper) hlowerY

end

end RHTower
