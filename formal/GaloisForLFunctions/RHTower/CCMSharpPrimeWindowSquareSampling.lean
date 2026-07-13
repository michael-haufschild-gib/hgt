import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowPrimeReduction

/-!
# Perfect-square sampling for the dyadic sharp prime window

The all-epsilon sharp dyadic von-Mangoldt estimate need only be checked at perfect-square
apertures.  For any positive `n`, the next strict square

`N = (floor(sqrt n) + 1)^2`

is at distance at most `2 * floor(sqrt n) + 1`.  The window at `n` is contained in the window at
`N` together with a lower boundary slice of that length.  The elementary bound
`Lambda(k) <= log k` makes the entire boundary cost `O(log N)`, which every positive power of
`n` absorbs.

Consequently a square-sample estimate with exponent `epsilon / 2` supplies the full estimate with
exponent `epsilon`.  Composing this source-pure transfer with the established sharp-window gate
shows that perfect-square samples alone force RH.
-/

open scoped BigOperators
open Finset ArithmeticFunction

noncomputable section

namespace RHTower

private theorem dyadicWeightedPrimeWindow_le_largerWindow_add_lowerSlice
    {n N : ℕ} (hN : n ≤ N) :
    dyadicWeightedPrimeWindow n ≤
      dyadicWeightedPrimeWindow N +
        ∑ k ∈ Ioc (n / 2) (N / 2),
          ArithmeticFunction.vonMangoldt k / Real.sqrt k := by
  rw [dyadicWeightedPrimeWindow, dyadicWeightedPrimeWindow]
  let f : ℕ → ℝ := fun k =>
    ArithmeticFunction.vonMangoldt k / Real.sqrt k
  have hsubset : Ioc (n / 2) n ⊆
      Ioc (N / 2) N ∪ Ioc (n / 2) (N / 2) := by
    intro k hk
    rw [mem_Ioc] at hk
    by_cases hkhalf : k ≤ N / 2
    · exact mem_union_right _ (mem_Ioc.mpr ⟨hk.1, hkhalf⟩)
    · exact mem_union_left _ (mem_Ioc.mpr ⟨lt_of_not_ge hkhalf, hk.2.trans hN⟩)
  have hnonneg : ∀ k : ℕ, 0 ≤ f k := fun k =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg k)
  have hdisj : Disjoint (Ioc (N / 2) N) (Ioc (n / 2) (N / 2)) :=
    Finset.disjoint_left.mpr (by
      intro k hkUpper hkLower
      rw [mem_Ioc] at hkUpper hkLower
      omega)
  calc
    (∑ k ∈ Ioc (n / 2) n, f k) ≤
        ∑ k ∈ Ioc (N / 2) N ∪ Ioc (n / 2) (N / 2), f k := by
      exact sum_le_sum_of_subset_of_nonneg hsubset
        (fun k _ _ => hnonneg k)
    _ ≤ (∑ k ∈ Ioc (N / 2) N, f k) +
        ∑ k ∈ Ioc (n / 2) (N / 2), f k := by
      rw [sum_union hdisj]

private theorem lowerSlice_le_log_gap
    {n N : ℕ} (hn : 0 < n) (hN : n ≤ N) :
    (∑ k ∈ Ioc (n / 2) (N / 2),
        ArithmeticFunction.vonMangoldt k / Real.sqrt k) ≤
      (((N - n : ℕ) : ℝ) * (Real.sqrt 2 / Real.sqrt n) * Real.log N) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hNpos : 0 < N := lt_of_lt_of_le hn hN
  have hlogN : 0 ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast hNpos)
  let B : ℝ := (Real.sqrt 2 / Real.sqrt n) * Real.log N
  have hterm : ∀ k ∈ Ioc (n / 2) (N / 2),
      ArithmeticFunction.vonMangoldt k / Real.sqrt k ≤ B := by
    intro k hk
    rw [mem_Ioc] at hk
    have hkpos : 0 < k := by omega
    have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
    have hsqrtk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkR
    have hnk : n ≤ 2 * k := by omega
    have hsqrt : Real.sqrt n ≤ Real.sqrt 2 * Real.sqrt k := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hnk)
    have hinv : 1 / Real.sqrt k ≤ Real.sqrt 2 / Real.sqrt n := by
      rw [div_le_div_iff₀ hsqrtk hsqrtn]
      simpa only [one_mul] using hsqrt
    have hkN : k ≤ N := by omega
    have hlog : Real.log k ≤ Real.log N :=
      Real.log_le_log hkR (by exact_mod_cast hkN)
    calc
      ArithmeticFunction.vonMangoldt k / Real.sqrt k ≤
          Real.log k / Real.sqrt k := by
        exact div_le_div_of_nonneg_right
          ArithmeticFunction.vonMangoldt_le_log (Real.sqrt_nonneg k)
      _ ≤ Real.log N / Real.sqrt k := by
        exact div_le_div_of_nonneg_right hlog (Real.sqrt_nonneg k)
      _ ≤ (Real.sqrt 2 / Real.sqrt n) * Real.log N := by
        rw [div_eq_mul_inv]
        simpa only [one_div, mul_comm] using
          mul_le_mul_of_nonneg_right hinv hlogN
  calc
    (∑ k ∈ Ioc (n / 2) (N / 2),
        ArithmeticFunction.vonMangoldt k / Real.sqrt k) ≤
        ∑ _k ∈ Ioc (n / 2) (N / 2), B :=
      sum_le_sum hterm
    _ = ((N / 2 - n / 2 : ℕ) : ℝ) * B := by
      rw [sum_const, Nat.card_Ioc]
      simp only [nsmul_eq_mul]
    _ ≤ ((N - n : ℕ) : ℝ) * B := by
      have hcard : N / 2 - n / 2 ≤ N - n := by omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (mul_nonneg (div_nonneg (Real.sqrt_nonneg 2) hsqrtn.le) hlogN)
    _ = ((N - n : ℕ) : ℝ) * (Real.sqrt 2 / Real.sqrt n) *
        Real.log N := by simp only [B]; ring

/-- Pointwise stability before simplifying the exact gap to the next strict square. -/
theorem dyadicWeightedPrimeWindow_le_upperSquare
    {n : ℕ} (hn : 0 < n) :
    dyadicWeightedPrimeWindow n ≤
      dyadicWeightedPrimeWindow ((Nat.sqrt n + 1) ^ 2) +
        ((((Nat.sqrt n + 1) ^ 2 - n : ℕ) : ℝ) *
          (Real.sqrt 2 / Real.sqrt n) *
          Real.log ((Nat.sqrt n + 1) ^ 2)) := by
  let N := (Nat.sqrt n + 1) ^ 2
  have hN : n ≤ N := (Nat.lt_succ_sqrt' n).le
  have hsplit := dyadicWeightedPrimeWindow_le_largerWindow_add_lowerSlice hN
  have hlower := lowerSlice_le_log_gap hn hN
  dsimp only [N] at hsplit hlower ⊢
  refine hsplit.trans ?_
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, add_comm] using
    (add_le_add_left hlower (dyadicWeightedPrimeWindow ((Nat.sqrt n + 1) ^ 2)))

/-- The change from an arbitrary aperture to the next strict square costs only logarithmically. -/
theorem dyadicWeightedPrimeWindow_le_upperSquare_add_log
    {n : ℕ} (hn : 0 < n) :
    dyadicWeightedPrimeWindow n ≤
      dyadicWeightedPrimeWindow ((Nat.sqrt n + 1) ^ 2) +
        3 * Real.sqrt 2 * Real.log ((Nat.sqrt n + 1) ^ 2) := by
  have hbase := dyadicWeightedPrimeWindow_le_upperSquare hn
  let r : ℕ := Nat.sqrt n
  let N : ℕ := (r + 1) ^ 2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hrSqNat : r ^ 2 ≤ n := by
    dsimp only [r]
    exact Nat.sqrt_le' n
  have hrle : (r : ℝ) ≤ Real.sqrt n := by
    have hrSq : (r : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hrSqNat
    exact (Real.le_sqrt (by positivity) hnR.le).mpr hrSq
  have hgapNat : N - n ≤ 2 * r + 1 := by
    rw [Nat.sub_le_iff_le_add]
    dsimp only [N]
    nlinarith [hrSqNat]
  have hgap : ((N - n : ℕ) : ℝ) ≤ 3 * Real.sqrt n := by
    have hgap' : ((N - n : ℕ) : ℝ) ≤ 2 * (r : ℝ) + 1 := by
      exact_mod_cast hgapNat
    have hsqrtOne : 1 ≤ Real.sqrt n :=
      Real.one_le_sqrt.mpr (by exact_mod_cast hn)
    linarith
  have hfactor :
      ((N - n : ℕ) : ℝ) * (Real.sqrt 2 / Real.sqrt n) ≤
        3 * Real.sqrt 2 := by
    rw [div_eq_mul_inv]
    have hinvnonneg : 0 ≤ (Real.sqrt n)⁻¹ := inv_nonneg.mpr hsqrtn.le
    calc
      ((N - n : ℕ) : ℝ) * (Real.sqrt 2 * (Real.sqrt n)⁻¹) =
          (((N - n : ℕ) : ℝ) * (Real.sqrt n)⁻¹) * Real.sqrt 2 := by ring
      _ ≤ ((3 * Real.sqrt n) * (Real.sqrt n)⁻¹) * Real.sqrt 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hgap hinvnonneg) (Real.sqrt_nonneg 2)
      _ = 3 * Real.sqrt 2 := by
        rw [show 3 * Real.sqrt n * (Real.sqrt n)⁻¹ * Real.sqrt 2 =
          3 * (Real.sqrt n * (Real.sqrt n)⁻¹) * Real.sqrt 2 by ring,
          mul_inv_cancel₀ hsqrtn.ne']
        ring
  have hNpos : 0 < N := by dsimp only [N]; positivity
  have hlog : 0 ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast hNpos)
  have herr :
      ((N - n : ℕ) : ℝ) * (Real.sqrt 2 / Real.sqrt n) * Real.log N ≤
        3 * Real.sqrt 2 * Real.log N :=
    mul_le_mul_of_nonneg_right hfactor hlog
  dsimp only [r, N] at herr
  refine hbase.trans ?_
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, add_comm] using
    (add_le_add_left herr (dyadicWeightedPrimeWindow ((Nat.sqrt n + 1) ^ 2)))

/-- An all-epsilon sharp-window estimate on perfect-square apertures extends to every aperture. -/
theorem eventually_dyadicWeightedPrimeWindow_upper_of_squareSamples
    {M : ℕ} (hM : 1 ≤ M)
    (hsquare : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, M ≤ m →
        dyadicWeightedPrimeWindow (m ^ 2) ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * (m : ℝ) +
            C * ((m ^ 2 : ℕ) : ℝ) ^ epsilon) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, M ^ 2 ≤ n →
        dyadicWeightedPrimeWindow n ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
            D * (n : ℝ) ^ epsilon := by
  intro epsilon hepsilon
  let delta : ℝ := epsilon / 2
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  obtain ⟨C, hC, htail⟩ := hsquare delta hdelta
  let c : ℝ := 2 * (1 - (Real.sqrt 2)⁻¹)
  let K : ℝ := (4 : ℝ) ^ delta
  let D : ℝ := c + C * K + 3 * Real.sqrt 2 * (K / delta)
  have hsqrtTwo : 1 ≤ Real.sqrt 2 :=
    Real.one_le_sqrt.mpr (by norm_num)
  have hinv : (Real.sqrt 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsqrtTwo
  have hc : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  refine ⟨D, hD, fun n hnM => ?_⟩
  have hn : 0 < n := lt_of_lt_of_le (by positivity : 0 < M ^ 2) hnM
  let m : ℕ := Nat.sqrt n + 1
  let N : ℕ := m ^ 2
  have hmM : M ≤ m := by
    have hMsq : M ^ 2 ≤ n := hnM
    have hMsqrt : M ≤ Nat.sqrt n := Nat.le_sqrt'.mpr hMsq
    dsimp only [m]
    omega
  have hsquareN := htail m hmM
  have hlocal := dyadicWeightedPrimeWindow_le_upperSquare_add_log hn
  have hNeq : N = (Nat.sqrt n + 1) ^ 2 := rfl
  rw [← hNeq] at hlocal
  have hrSqNat : (Nat.sqrt n) ^ 2 ≤ n := Nat.sqrt_le' n
  have hrle : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := by
    have hrSq : (Nat.sqrt n : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hrSqNat
    have hnR : (0 : ℝ) ≤ n := by positivity
    exact (Real.le_sqrt (by positivity) hnR).mpr hrSq
  have hmle : (m : ℝ) ≤ Real.sqrt n + 1 := by
    dsimp only [m]
    push_cast
    linarith
  have hN4Nat : N ≤ 4 * n := by
    have hrpos : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr hn
    dsimp only [N, m]
    nlinarith
  have hN4 : (N : ℝ) ≤ 4 * (n : ℝ) := by exact_mod_cast hN4Nat
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpowOne : 1 ≤ (n : ℝ) ^ epsilon :=
    Real.one_le_rpow hnOne hepsilon.le
  have hpowExp : (n : ℝ) ^ delta ≤ (n : ℝ) ^ epsilon := by
    apply Real.rpow_le_rpow_of_exponent_le hnOne
    dsimp only [delta]
    linarith
  have hNpow : (N : ℝ) ^ delta ≤ K * (n : ℝ) ^ epsilon := by
    calc
      (N : ℝ) ^ delta ≤ (4 * (n : ℝ)) ^ delta :=
        Real.rpow_le_rpow (by positivity) hN4 hdelta.le
      _ = (4 : ℝ) ^ delta * (n : ℝ) ^ delta := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity)]
      _ ≤ (4 : ℝ) ^ delta * (n : ℝ) ^ epsilon :=
        mul_le_mul_of_nonneg_left hpowExp (by positivity)
      _ = K * (n : ℝ) ^ epsilon := rfl
  have hlog : Real.log N ≤ (K / delta) * (n : ℝ) ^ epsilon := by
    have hraw := Real.log_le_rpow_div (x := (N : ℝ))
      (by positivity) hdelta
    calc
      Real.log N ≤ (N : ℝ) ^ delta / delta := hraw
      _ ≤ (K * (n : ℝ) ^ epsilon) / delta := by
        exact div_le_div_of_nonneg_right hNpow hdelta.le
      _ = (K / delta) * (n : ℝ) ^ epsilon := by ring
  have hmain : c * (m : ℝ) ≤
      c * Real.sqrt n + c * (n : ℝ) ^ epsilon := by
    have hm := mul_le_mul_of_nonneg_left hmle hc
    calc
      c * (m : ℝ) ≤ c * (Real.sqrt n + 1) := hm
      _ = c * Real.sqrt n + c := by ring
      _ ≤ c * Real.sqrt n + c * (n : ℝ) ^ epsilon := by
        nlinarith [mul_le_mul_of_nonneg_left hpowOne hc]
  have hsample : dyadicWeightedPrimeWindow N ≤
      c * Real.sqrt n + (c + C * K) * (n : ℝ) ^ epsilon := by
    have hCpow : C * (N : ℝ) ^ delta ≤
        C * (K * (n : ℝ) ^ epsilon) :=
      mul_le_mul_of_nonneg_left hNpow hC
    change dyadicWeightedPrimeWindow N ≤ c * (m : ℝ) +
      C * (N : ℝ) ^ delta at hsquareN
    calc
      dyadicWeightedPrimeWindow N ≤ c * (m : ℝ) + C * (N : ℝ) ^ delta := hsquareN
      _ ≤ (c * Real.sqrt n + c * (n : ℝ) ^ epsilon) +
          C * (K * (n : ℝ) ^ epsilon) := add_le_add hmain hCpow
      _ = c * Real.sqrt n + (c + C * K) * (n : ℝ) ^ epsilon := by ring
  have hlogCost : 3 * Real.sqrt 2 * Real.log N ≤
      (3 * Real.sqrt 2 * (K / delta)) * (n : ℝ) ^ epsilon := by
    have hcoef : 0 ≤ 3 * Real.sqrt 2 := by positivity
    have h := mul_le_mul_of_nonneg_left hlog hcoef
    simpa only [mul_assoc] using h
  have hlocalN : dyadicWeightedPrimeWindow n ≤
      dyadicWeightedPrimeWindow N + 3 * Real.sqrt 2 * Real.log N := by
    simpa only [N, m, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hlocal
  calc
    dyadicWeightedPrimeWindow n ≤
        dyadicWeightedPrimeWindow N + 3 * Real.sqrt 2 * Real.log N := hlocalN
    _ ≤ (c * Real.sqrt n + (c + C * K) * (n : ℝ) ^ epsilon) +
        (3 * Real.sqrt 2 * (K / delta)) * (n : ℝ) ^ epsilon :=
      add_le_add hsample hlogCost
    _ = 2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
        D * (n : ℝ) ^ epsilon := by
      dsimp only [c, D]
      ring

/-- The full all-epsilon estimate is equivalent to its restriction to perfect squares. -/
theorem eventually_dyadicWeightedPrimeWindow_upper_iff_squareSamples
    {M : ℕ} (hM : 1 ≤ M) :
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, M ^ 2 ≤ n →
        dyadicWeightedPrimeWindow n ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
            C * (n : ℝ) ^ epsilon) ↔
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, M ≤ m →
        dyadicWeightedPrimeWindow (m ^ 2) ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * (m : ℝ) +
            C * ((m ^ 2 : ℕ) : ℝ) ^ epsilon) := by
  constructor
  · intro hfull epsilon hepsilon
    obtain ⟨C, hC, htail⟩ := hfull epsilon hepsilon
    refine ⟨C, hC, fun m hm => ?_⟩
    have hcut : M ^ 2 ≤ m ^ 2 := by nlinarith
    have h := htail (m ^ 2) hcut
    simpa only [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg m)] using h
  · exact eventually_dyadicWeightedPrimeWindow_upper_of_squareSamples hM

/-- On square apertures, removing every proper prime power preserves the all-epsilon estimate. -/
theorem squareSample_dyadicWeightedPrimeWindow_upper_iff_primeOnly
    {M : ℕ} (hM : 1 ≤ M) :
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, M ≤ m →
        dyadicWeightedPrimeWindow (m ^ 2) ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * (m : ℝ) +
            C * ((m ^ 2 : ℕ) : ℝ) ^ epsilon) ↔
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, M ≤ m →
        dyadicWeightedPrimeOnlyWindow (m ^ 2) ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * (m : ℝ) +
            C * ((m ^ 2 : ℕ) : ℝ) ^ epsilon) := by
  constructor
  · intro hfull epsilon hepsilon
    obtain ⟨C, hC, htail⟩ := hfull epsilon hepsilon
    refine ⟨C, hC, fun m hm => ?_⟩
    exact (dyadicWeightedPrimeOnlyWindow_le_window (m ^ 2)).trans (htail m hm)
  · intro hprime epsilon hepsilon
    obtain ⟨C, hC, htail⟩ := hprime epsilon hepsilon
    let D : ℝ := C + 2 * Real.sqrt 2 / epsilon
    have hD : 0 ≤ D := by dsimp only [D]; positivity
    refine ⟨D, hD, fun m hm => ?_⟩
    have hmpos : 0 < m := lt_of_lt_of_le (by omega : 0 < M) hm
    have hsqOne : 1 ≤ m ^ 2 := by nlinarith
    have hprimeN : dyadicWeightedPrimeOnlyWindow (m ^ 2) ≤
        2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt ((m ^ 2 : ℕ) : ℝ) +
          C * ((m ^ 2 : ℕ) : ℝ) ^ epsilon := by
      simpa only [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg m)] using htail m hm
    have h := dyadicWeightedPrimeWindow_upper_of_primeOnlyWindow_upper
      hsqOne hepsilon hprimeN
    simpa only [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg m), D] using h

/-- At square apertures, the remaining prime-only estimate is exactly the one-sided increment
of the prime Chebyshev error `theta(x) - x`. -/
theorem squareSample_dyadicWeightedPrimeOnlyWindow_upper_iff_thetaErrorIncrement
    {M : ℕ} (hM : 2 ≤ M) :
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, M ≤ m →
        dyadicWeightedPrimeOnlyWindow (m ^ 2) ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * (m : ℝ) +
            C * ((m ^ 2 : ℕ) : ℝ) ^ epsilon) ↔
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, M ≤ m →
        dyadicCriticalThetaMellinErrorIncrement (m ^ 2) ≤
          C * ((m ^ 2 : ℕ) : ℝ) ^ epsilon) := by
  constructor
  · intro hprime epsilon hepsilon
    obtain ⟨C, hC, htail⟩ := hprime epsilon hepsilon
    refine ⟨C, hC, fun m hm => ?_⟩
    have hmTwo : 2 ≤ m := hM.trans hm
    have hsqTwo : 2 ≤ m ^ 2 := by nlinarith
    have h := (dyadicWeightedPrimeOnlyWindow_upper_iff_thetaErrorIncrement
      hsqTwo C epsilon).mp ?_
    · exact h
    · simpa only [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg m)] using htail m hm
  · intro htheta epsilon hepsilon
    obtain ⟨C, hC, htail⟩ := htheta epsilon hepsilon
    refine ⟨C, hC, fun m hm => ?_⟩
    have hmTwo : 2 ≤ m := hM.trans hm
    have hsqTwo : 2 ≤ m ^ 2 := by nlinarith
    have h := (dyadicWeightedPrimeOnlyWindow_upper_iff_thetaErrorIncrement
      hsqTwo C epsilon).mpr (htail m hm)
    simpa only [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg m)] using h

/-- The original full-aperture inequality is equivalent to a theta-error value relation only at
perfect squares. -/
theorem eventually_dyadicWeightedPrimeWindow_upper_iff_squareThetaErrorIncrement
    {M : ℕ} (hM : 2 ≤ M) :
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, M ^ 2 ≤ n →
        dyadicWeightedPrimeWindow n ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
            C * (n : ℝ) ^ epsilon) ↔
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, M ≤ m →
        dyadicCriticalThetaMellinErrorIncrement (m ^ 2) ≤
          C * ((m ^ 2 : ℕ) : ℝ) ^ epsilon) := by
  exact (eventually_dyadicWeightedPrimeWindow_upper_iff_squareSamples
    (hM.trans' (by omega))).trans
      ((squareSample_dyadicWeightedPrimeWindow_upper_iff_primeOnly
        (hM.trans' (by omega))).trans
        (squareSample_dyadicWeightedPrimeOnlyWindow_upper_iff_thetaErrorIncrement hM))

/-- Perfect-square samples alone discharge the sharp dyadic prime-window RH gate. -/
theorem riemannHypothesis_of_eventually_dyadicWeightedPrimeWindow_square_upper
    {M : ℕ} (hM : 1 ≤ M)
    (hsquare : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, M ≤ m →
        dyadicWeightedPrimeWindow (m ^ 2) ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * (m : ℝ) +
            C * ((m ^ 2 : ℕ) : ℝ) ^ epsilon) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_eventually_dyadicWeightedPrimeWindow_upper
  exact eventually_dyadicWeightedPrimeWindow_upper_of_squareSamples hM hsquare

/-- A one-sided subpower bound for the prime Chebyshev error increment only at perfect squares
already proves RH. -/
theorem riemannHypothesis_of_eventually_squareThetaErrorIncrement_upper
    {M : ℕ} (hM : 2 ≤ M)
    (htheta : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, M ≤ m →
        dyadicCriticalThetaMellinErrorIncrement (m ^ 2) ≤
          C * ((m ^ 2 : ℕ) : ℝ) ^ epsilon) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_eventually_dyadicWeightedPrimeWindow_upper
  exact (eventually_dyadicWeightedPrimeWindow_upper_iff_squareThetaErrorIncrement hM).mpr
    htheta

end RHTower
