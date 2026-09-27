import GaloisForLFunctions.RHTower.MobiusTwoJetBlockTaylor
import GaloisForLFunctions.RHTower.WindowBudget
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinEveryBaseThetaMass

/-!
# Balanced prime–semiprime two-jet packets with a cofactor

Let `α = 71/100`.  The every-base theta-mass theorem gives
`θ(z + z^α/2) - θ(z) > z^α/16384` for all large `z`, hence at least `z^α/(16384 log 5R)` primes
in each window `(z, z + z^α/2]` below `5R`.

For a cofactor `q ≥ 1` with `q² ≤ R` put `H = q(4R/q)^α`, `L = 8H`, `J = ⌊2R/L⌋`,
`m = ⌊(R/q)^α/(32768 log 5R)⌋`, and split `[2R, 4R)` into the blocks `[2R + jL, 2R + (j+1)L)`.
In the two outer quarters of every block the windows at the bases `X/q` and `X/(2q)` supply `m`
atoms `qp` and `m` atoms `2qr` each; the balanced selection of `MobiusTwoJetBlockTaylor` keeps unit
coefficients and one orientation complete.  Summing the block bounds over the `J` blocks gives,
uniformly in `0 ≤ δ ≤ 1` and in the cofactor,

`‖Σ_r f_{2qr} - Σ_p f_{qp}‖_δ ≤ C [R^{-(1+δ)/2} + R^{-2/25-δ/2} q^{-21/50} / log R]`,

with `R < qr < 2R`, `2R < qp < 4R`, equally many `r` and `p`, and at least `c R/(q log R)` of each.
The exponent `-2/25 = 2α - 3/2` and the cofactor exponent `-21/50 = 1 - 2α`.
-/

open Finset Filter Topology

noncomputable section

namespace RHTower.CubicGamma

/-- The prime supply exponent `α = 71/100`. -/
def supplyExp : ℝ := 71 / 100

theorem supplyExp_pos : 0 < supplyExp := by norm_num [supplyExp]

theorem supplyExp_lt_one : supplyExp < 1 := by norm_num [supplyExp]

/-! ### Prime supply in short windows -/

/-- The every-base theta mass at exponent `71/100`. -/
theorem exists_theta_window_supply :
    ∃ z₀ : ℝ, 1 ≤ z₀ ∧ ∀ z : ℝ, z₀ ≤ z →
      z ^ supplyExp / 16384 <
        Chebyshev.theta (z + z ^ supplyExp / 2) - Chebyshev.theta z := by
  have h := RHTower.Sieve.eventually_routeT_detectorPacking_theta_mass_every_base
    (alpha := supplyExp) (by norm_num [supplyExp]) supplyExp_lt_one
  obtain ⟨z₁, hz₁⟩ := eventually_atTop.mp h
  exact ⟨max 1 z₁, le_max_left _ _, fun z hz => hz₁ z (le_of_max_le_right hz)⟩

/-- A window with theta mass above `z^α/16384` below `e^Λ` holds at least `z^α/(16384 Λ)`
primes. -/
theorem card_windowPrimes_ge {z Λ : ℝ} (hz : 1 ≤ z)
    (hθ : z ^ supplyExp / 16384 <
      Chebyshev.theta (z + z ^ supplyExp / 2) - Chebyshev.theta z)
    (hΛ : Real.log (z + z ^ supplyExp / 2) ≤ Λ) :
    z ^ supplyExp / (16384 * Λ) ≤ (windowPrimes z (z + z ^ supplyExp / 2)).card := by
  have hzα : 0 < z ^ supplyExp := Real.rpow_pos_of_pos (by linarith) _
  have hy : z ≤ z + z ^ supplyExp / 2 := by linarith
  have hy1 : 1 < z + z ^ supplyExp / 2 := by linarith
  have hlog : 0 < Real.log (z + z ^ supplyExp / 2) := Real.log_pos hy1
  have hΛ0 : 0 < Λ := hlog.trans_le hΛ
  have hsum := sum_log_windowPrimes hy
  have hle : ∑ p ∈ windowPrimes z (z + z ^ supplyExp / 2), Real.log p ≤
      (windowPrimes z (z + z ^ supplyExp / 2)).card * Λ := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply sum_le_sum
    intro p hp
    have hp' := (mem_windowPrimes (by linarith) (by linarith)).mp hp
    have hp0 : (0 : ℝ) < p := by linarith [hp'.2.1]
    exact (Real.log_le_log hp0 hp'.2.2).trans hΛ
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- `m` distinct primes from a window holding at least `m` of them. -/
theorem exists_injective_windowPrimes {z y : ℝ} (hz : 0 ≤ z) (hzy : z ≤ y) (m : ℕ)
    (hm : (m : ℝ) ≤ (windowPrimes z y).card) :
    ∃ e : ℕ → ℕ, (∀ i < m, (e i).Prime ∧ z < e i ∧ (e i : ℝ) ≤ y) ∧
      ∀ i < m, ∀ j < m, e i = e j → i = j := by
  have hm' : m ≤ (windowPrimes z y).card := by exact_mod_cast hm
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hm'
  refine ⟨fun i => if h : i < m then T.orderEmbOfFin hTc ⟨i, h⟩ else 0, fun i hi => ?_,
    fun i hi j hj hij => ?_⟩
  · simp only [hi, ↓reduceDIte]
    have hmem := hT (T.orderEmbOfFin_mem hTc ⟨i, hi⟩)
    exact (mem_windowPrimes hz (hz.trans hzy)).mp hmem
  · simp only [hi, hj, ↓reduceDIte] at hij
    have := (T.orderEmbOfFin hTc).injective hij
    simpa using this

/-! ### One block -/

/-- `q z^α ≤ H = q (4R/q)^α` for `0 ≤ z ≤ 4R/q`. -/
theorem cofactor_rpow_le {q : ℕ} (hq : 1 ≤ q) {R z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 4 * R / q) :
    (q : ℝ) * z ^ supplyExp ≤ q * (4 * R / q) ^ supplyExp := by
  have hq0 : (0 : ℝ) ≤ q := by positivity
  gcongr
  exact supplyExp_pos.le

/-- `m` distinct primes in the window `(z, z + z^α/2]` for every base `z ≥ R/q` below `5R`. -/
theorem exists_window_family {z₀ : ℝ} (hz₀ : 1 ≤ z₀)
    (hsupply : ∀ z : ℝ, z₀ ≤ z → z ^ supplyExp / 16384 <
      Chebyshev.theta (z + z ^ supplyExp / 2) - Chebyshev.theta z)
    {R : ℝ} (hR : 1 ≤ R) {q : ℕ} (hRq : z₀ ≤ R / q) (m : ℕ)
    (hm : (m : ℝ) ≤ (R / q) ^ supplyExp / (16384 * Real.log (5 * R)))
    {z : ℝ} (hzR : R / q ≤ z) (hy : z + z ^ supplyExp / 2 ≤ 5 * R) :
    ∃ e : ℕ → ℕ, (∀ i < m, (e i).Prime ∧ z < e i ∧ (e i : ℝ) ≤ z + z ^ supplyExp / 2) ∧
      ∀ i < m, ∀ j < m, e i = e j → i = j := by
  have hz0 : z₀ ≤ z := hRq.trans hzR
  have hz1 : 1 ≤ z := hz₀.trans hz0
  have hΛ : Real.log (z + z ^ supplyExp / 2) ≤ Real.log (5 * R) :=
    Real.log_le_log (by have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ z) supplyExp; positivity) hy
  have hcard := card_windowPrimes_ge hz1 (hsupply z hz0) hΛ
  have hRq0 : 0 ≤ R / q := (by linarith : (0 : ℝ) ≤ 1).trans (hz₀.trans hRq)
  have hmono : (R / q) ^ supplyExp ≤ z ^ supplyExp :=
    Real.rpow_le_rpow hRq0 hzR supplyExp_pos.le
  have hlog5 : 0 < Real.log (5 * R) := Real.log_pos (by linarith)
  have hm' : (m : ℝ) ≤ (windowPrimes z (z + z ^ supplyExp / 2)).card := by
    refine hm.trans (le_trans ?_ hcard)
    gcongr
  exact exists_injective_windowPrimes (by linarith)
    (by have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ z) supplyExp; linarith) m hm'

/-- A prime window at base `Z/q` places the atoms `qp` in `(Z, Z + H]`. -/
theorem cofactor_prime_atoms {q : ℕ} (hq : 1 ≤ q) {R Z : ℝ} (hZ0 : 0 ≤ Z) (hZ : Z ≤ 4 * R)
    {p : ℕ} (hp1 : Z / q < p) (hp2 : (p : ℝ) ≤ Z / q + (Z / q) ^ supplyExp / 2) :
    Z < ((q * p : ℕ) : ℝ) ∧ ((q * p : ℕ) : ℝ) ≤ Z + q * (4 * R / q) ^ supplyExp := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hzq : Z / q ≤ 4 * R / q := div_le_div_of_nonneg_right hZ hq0.le
  have hH := cofactor_rpow_le hq (div_nonneg hZ0 hq0.le) hzq
  have hr0 : 0 ≤ (Z / q) ^ supplyExp := Real.rpow_nonneg (div_nonneg hZ0 hq0.le) _
  push_cast
  constructor
  · have := mul_lt_mul_of_pos_left hp1 hq0
    rwa [mul_div_cancel₀ _ hq0.ne'] at this
  · have := mul_le_mul_of_nonneg_left hp2 hq0.le
    rw [mul_add, mul_div_cancel₀ _ hq0.ne'] at this
    nlinarith

/-- A prime window at base `Z/(2q)` places the atoms `2qr` in `(Z, Z + H]`. -/
theorem cofactor_doubled_atoms {q : ℕ} (hq : 1 ≤ q) {R Z : ℝ} (hZ0 : 0 ≤ Z) (hZ : Z ≤ 4 * R)
    {r : ℕ} (hr1 : Z / (2 * q) < r) (hr2 : (r : ℝ) ≤ Z / (2 * q) + (Z / (2 * q)) ^ supplyExp / 2) :
    Z < ((2 * q * r : ℕ) : ℝ) ∧ ((2 * q * r : ℕ) : ℝ) ≤ Z + q * (4 * R / q) ^ supplyExp := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have h2q : (0 : ℝ) < 2 * q := by positivity
  have hzq : Z / (2 * q) ≤ 4 * R / q := by
    rw [div_le_div_iff₀ h2q hq0]
    nlinarith
  have hH := cofactor_rpow_le hq (div_nonneg hZ0 h2q.le) hzq
  push_cast
  constructor
  · have := mul_lt_mul_of_pos_left hr1 h2q
    rwa [mul_div_cancel₀ _ h2q.ne'] at this
  · have := mul_le_mul_of_nonneg_left hr2 h2q.le
    rw [mul_add, mul_div_cancel₀ _ h2q.ne'] at this
    nlinarith

/-- **One balanced cofactor block** at `X ∈ [2R, 4R - 8H]`, `H = q(4R/q)^α`. -/
theorem exists_cofactor_block {z₀ : ℝ} (hz₀ : 1 ≤ z₀)
    (hsupply : ∀ z : ℝ, z₀ ≤ z → z ^ supplyExp / 16384 <
      Chebyshev.theta (z + z ^ supplyExp / 2) - Chebyshev.theta z)
    {R : ℝ} (hR : 1 ≤ R) {q : ℕ} (hq : 1 ≤ q) (hRq : z₀ ≤ R / q)
    {X : ℝ} (hX : 2 * R ≤ X) (hXL : X + 8 * (q * (4 * R / q) ^ supplyExp) ≤ 4 * R)
    (hLX : 8 * (q * (4 * R / q) ^ supplyExp) ≤ X)
    (m : ℕ) (hm : (m : ℝ) ≤ (R / q) ^ supplyExp / (16384 * Real.log (5 * R))) :
    ∃ rN rP pN pP : ℕ → ℕ, ∃ su sv : ℕ, su ≤ m ∧ sv ≤ m ∧ (su = m ∨ sv = m) ∧
      (∀ i < m, (rN i).Prime ∧ X < ((2 * q * rN i : ℕ) : ℝ) ∧
        ((2 * q * rN i : ℕ) : ℝ) ≤ X + q * (4 * R / q) ^ supplyExp) ∧
      (∀ i < m, (rP i).Prime ∧ X + 6 * (q * (4 * R / q) ^ supplyExp) < ((2 * q * rP i : ℕ) : ℝ) ∧
        ((2 * q * rP i : ℕ) : ℝ) ≤ X + 7 * (q * (4 * R / q) ^ supplyExp)) ∧
      (∀ i < m, (pN i).Prime ∧ X < ((q * pN i : ℕ) : ℝ) ∧
        ((q * pN i : ℕ) : ℝ) ≤ X + q * (4 * R / q) ^ supplyExp) ∧
      (∀ i < m, (pP i).Prime ∧ X + 6 * (q * (4 * R / q) ^ supplyExp) < ((q * pP i : ℕ) : ℝ) ∧
        ((q * pP i : ℕ) : ℝ) ≤ X + 7 * (q * (4 * R / q) ^ supplyExp)) ∧
      (∀ i < m, ∀ j < m, rN i = rN j → i = j) ∧ (∀ i < m, ∀ j < m, rP i = rP j → i = j) ∧
      (∀ i < m, ∀ j < m, pN i = pN j → i = j) ∧ (∀ i < m, ∀ j < m, pP i = pP j → i = j) ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        gammaNorm δ (fun t => ∑ i ∈ range su,
            (atom ((2 * q * rN i : ℕ) : ℝ) t - atom ((q * pP i : ℕ) : ℝ) t) +
          ∑ i ∈ range sv, (atom ((2 * q * rP i : ℕ) : ℝ) t - atom ((q * pN i : ℕ) : ℝ) t)) ≤
          jetConst 1 * (8 * (q * (4 * R / q) ^ supplyExp)) * X * (X ^ ((5 + δ) / 2))⁻¹ +
            8 * m * (8 * (q * (4 * R / q) ^ supplyExp)) ^ 2 * jetConst 2 *
              (X ^ ((5 + δ) / 2))⁻¹ := by
  set H : ℝ := q * (4 * R / q) ^ supplyExp with hHdef
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hR0 : 0 < R := by linarith
  have hH0 : 0 < H := by
    rw [hHdef]
    have := Real.rpow_pos_of_pos (by positivity : 0 < 4 * R / q) supplyExp
    positivity
  have hX0 : 0 < X := by linarith
  have hX4 : X + 6 * H ≤ 4 * R := by linarith
  -- bases of the four windows
  have hbase1 : R / q ≤ X / q := div_le_div_of_nonneg_right (by linarith) hq0.le
  have hbase2 : R / q ≤ (X + 6 * H) / q := div_le_div_of_nonneg_right (by linarith) hq0.le
  have hbase3 : R / q ≤ X / (2 * q) := by
    rw [div_le_div_iff₀ hq0 (by positivity)]; nlinarith
  have hbase4 : R / q ≤ (X + 6 * H) / (2 * q) := by
    rw [div_le_div_iff₀ hq0 (by positivity)]; nlinarith
  -- tops of the four windows below `5R`
  have htopP : ∀ Z : ℝ, 0 ≤ Z → Z ≤ X + 6 * H →
      Z / q + (Z / q) ^ supplyExp / 2 ≤ 5 * R := by
    intro Z hZ0 hZ
    have hzq : Z / q ≤ 4 * R / q := div_le_div_of_nonneg_right (by linarith) hq0.le
    have hH := cofactor_rpow_le hq (div_nonneg hZ0 hq0.le) hzq
    have e : q * (Z / q + (Z / q) ^ supplyExp / 2) = Z + q * (Z / q) ^ supplyExp / 2 := by
      field_simp
    have h1 : q * (Z / q + (Z / q) ^ supplyExp / 2) ≤ 4 * R := by rw [e]; linarith
    have h2 : 0 ≤ Z / q + (Z / q) ^ supplyExp / 2 := by
      have := Real.rpow_nonneg (div_nonneg hZ0 hq0.le) supplyExp; positivity
    nlinarith
  have htopD : ∀ Z : ℝ, 0 ≤ Z → Z ≤ X + 6 * H →
      Z / (2 * q) + (Z / (2 * q)) ^ supplyExp / 2 ≤ 5 * R := by
    intro Z hZ0 hZ
    have h2q : (0 : ℝ) < 2 * q := by positivity
    have hzq : Z / (2 * q) ≤ 4 * R / q := by
      rw [div_le_div_iff₀ h2q hq0]; nlinarith
    have hH := cofactor_rpow_le hq (div_nonneg hZ0 h2q.le) hzq
    have e : 2 * q * (Z / (2 * q) + (Z / (2 * q)) ^ supplyExp / 2) =
        Z + q * (Z / (2 * q)) ^ supplyExp := by
      field_simp
    have h1 : 2 * q * (Z / (2 * q) + (Z / (2 * q)) ^ supplyExp / 2) ≤ 4 * R := by
      rw [e]; linarith
    have h2 : 0 ≤ Z / (2 * q) + (Z / (2 * q)) ^ supplyExp / 2 := by
      have := Real.rpow_nonneg (div_nonneg hZ0 h2q.le) supplyExp; positivity
    nlinarith
  obtain ⟨pN, hpN, ipN⟩ := exists_window_family hz₀ hsupply hR hRq m hm hbase1
    (htopP X hX0.le (by linarith))
  obtain ⟨pP, hpP, ipP⟩ := exists_window_family hz₀ hsupply hR hRq m hm hbase2
    (htopP (X + 6 * H) (by linarith) le_rfl)
  obtain ⟨rN, hrN, irN⟩ := exists_window_family hz₀ hsupply hR hRq m hm hbase3
    (htopD X hX0.le (by linarith))
  obtain ⟨rP, hrP, irP⟩ := exists_window_family hz₀ hsupply hR hRq m hm hbase4
    (htopD (X + 6 * H) (by linarith) le_rfl)
  have posN : ∀ i < m, X < ((q * pN i : ℕ) : ℝ) ∧ ((q * pN i : ℕ) : ℝ) ≤ X + H := fun i hi =>
    cofactor_prime_atoms hq hX0.le (by linarith) (hpN i hi).2.1 (hpN i hi).2.2
  have posP : ∀ i < m, X + 6 * H < ((q * pP i : ℕ) : ℝ) ∧
      ((q * pP i : ℕ) : ℝ) ≤ X + 7 * H := fun i hi => by
    have h := cofactor_prime_atoms hq (by linarith) hX4 (hpP i hi).2.1 (hpP i hi).2.2
    exact ⟨h.1, by linarith [h.2]⟩
  have posRN : ∀ i < m, X < ((2 * q * rN i : ℕ) : ℝ) ∧
      ((2 * q * rN i : ℕ) : ℝ) ≤ X + H := fun i hi =>
    cofactor_doubled_atoms hq hX0.le (by linarith) (hrN i hi).2.1 (hrN i hi).2.2
  have posRP : ∀ i < m, X + 6 * H < ((2 * q * rP i : ℕ) : ℝ) ∧
      ((2 * q * rP i : ℕ) : ℝ) ≤ X + 7 * H := fun i hi => by
    have h := cofactor_doubled_atoms hq (by linarith) hX4 (hrP i hi).2.1 (hrP i hi).2.2
    exact ⟨h.1, by linarith [h.2]⟩
  obtain ⟨su, sv, hsu, hsv, hend, hbound⟩ := exists_block_two_jet hX0 (by linarith : 0 ≤ 8 * H)
    hLX m (fun i => ((2 * q * rN i : ℕ) : ℝ)) (fun i => ((q * pP i : ℕ) : ℝ))
    (fun i => ((2 * q * rP i : ℕ) : ℝ)) (fun i => ((q * pN i : ℕ) : ℝ))
    (fun i hi => ⟨(posRN i hi).1.le, by linarith [(posRN i hi).2]⟩)
    (fun i hi => ⟨by linarith [(posP i hi).1], by linarith [(posP i hi).2]⟩)
    (fun i hi => ⟨by linarith [(posRP i hi).1], by linarith [(posRP i hi).2]⟩)
    (fun i hi => ⟨(posN i hi).1.le, by linarith [(posN i hi).2]⟩)
  exact ⟨rN, rP, pN, pP, su, sv, hsu, hsv, hend,
    fun i hi => ⟨(hrN i hi).1, posRN i hi⟩, fun i hi => ⟨(hrP i hi).1, posRP i hi⟩,
    fun i hi => ⟨(hpN i hi).1, posN i hi⟩, fun i hi => ⟨(hpP i hi).1, posP i hi⟩,
    irN, irP, ipN, ipP, hbound⟩

/-! ### Assembly of the blocks -/

/-- The atoms of one block: a prefix of the family `a` and a prefix of the family `b`. -/
def blockSet (su sv : ℕ → ℕ) (a b : ℕ → ℕ → ℕ) (j : ℕ) : Finset ℕ :=
  (range (su j)).image (a j) ∪ (range (sv j)).image (b j)

/-- All blocks `j < J`. -/
def packetSet (J : ℕ) (su sv : ℕ → ℕ) (a b : ℕ → ℕ → ℕ) : Finset ℕ :=
  (range J).biUnion (blockSet su sv a b)

theorem card_blockSet {su sv : ℕ → ℕ} {a b : ℕ → ℕ → ℕ} {j m : ℕ} (hsu : su j ≤ m)
    (hsv : sv j ≤ m) (ia : ∀ i < m, ∀ i' < m, a j i = a j i' → i = i')
    (ib : ∀ i < m, ∀ i' < m, b j i = b j i' → i = i') (hab : ∀ i < m, ∀ i' < m, a j i ≠ b j i') :
    (blockSet su sv a b j).card = su j + sv j := by
  unfold blockSet
  rw [card_union_of_disjoint, card_image_of_injOn, card_image_of_injOn, card_range, card_range]
  · intro i hi i' hi' h
    exact ib i (by have := mem_range.mp hi; omega) i' (by have := mem_range.mp hi'; omega) h
  · intro i hi i' hi' h
    exact ia i (by have := mem_range.mp hi; omega) i' (by have := mem_range.mp hi'; omega) h
  · rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    obtain ⟨i', hi', he⟩ := mem_image.mp hx'
    exact hab i (by have := mem_range.mp hi; omega) i' (by have := mem_range.mp hi'; omega) he.symm

theorem sum_blockSet (f : ℕ → ℝ) {su sv : ℕ → ℕ} {a b : ℕ → ℕ → ℕ} {j m : ℕ} (hsu : su j ≤ m)
    (hsv : sv j ≤ m) (ia : ∀ i < m, ∀ i' < m, a j i = a j i' → i = i')
    (ib : ∀ i < m, ∀ i' < m, b j i = b j i' → i = i') (hab : ∀ i < m, ∀ i' < m, a j i ≠ b j i') :
    ∑ x ∈ blockSet su sv a b j, f x =
      ∑ i ∈ range (su j), f (a j i) + ∑ i ∈ range (sv j), f (b j i) := by
  unfold blockSet
  rw [sum_union, sum_image, sum_image]
  · intro i hi i' hi' h
    exact ib i (by have := mem_range.mp hi; omega) i' (by have := mem_range.mp hi'; omega) h
  · intro i hi i' hi' h
    exact ia i (by have := mem_range.mp hi; omega) i' (by have := mem_range.mp hi'; omega) h
  · rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    obtain ⟨i', hi', he⟩ := mem_image.mp hx'
    exact hab i (by have := mem_range.mp hi; omega) i' (by have := mem_range.mp hi'; omega) he.symm

theorem mem_blockSet {su sv : ℕ → ℕ} {a b : ℕ → ℕ → ℕ} {j x : ℕ} :
    x ∈ blockSet su sv a b j ↔ (∃ i < su j, a j i = x) ∨ ∃ i < sv j, b j i = x := by
  unfold blockSet
  simp [mem_union, mem_image, mem_range]

/-- Blocks at spacing `8H` whose atoms lie in `(X_j, X_j + 7H]` are pairwise disjoint. -/
theorem pairwiseDisjoint_blockSet (φ : ℕ → ℝ) {J : ℕ} {su sv : ℕ → ℕ} {a b : ℕ → ℕ → ℕ}
    {X₀ H : ℝ} (hH : 0 < H)
    (hpos : ∀ j < J, ∀ x ∈ blockSet su sv a b j,
      X₀ + j * (8 * H) < φ x ∧ φ x ≤ X₀ + j * (8 * H) + 7 * H) :
    (↑(range J) : Set ℕ).PairwiseDisjoint (blockSet su sv a b) := by
  intro j hj j' hj' hne
  rw [Function.onFun, Finset.disjoint_left]
  intro x hx hx'
  have hj0 := hpos j (mem_range.mp hj) x hx
  have hj1 := hpos j' (mem_range.mp hj') x hx'
  rcases lt_or_gt_of_ne hne with h | h
  · have : (j : ℝ) + 1 ≤ j' := by exact_mod_cast h
    nlinarith
  · have : (j' : ℝ) + 1 ≤ j := by exact_mod_cast h
    nlinarith

theorem card_packetSet (φ : ℕ → ℝ) {J m : ℕ} {su sv : ℕ → ℕ} {a b : ℕ → ℕ → ℕ} {X₀ H : ℝ}
    (hH : 0 < H)
    (hpos : ∀ j < J, ∀ x ∈ blockSet su sv a b j,
      X₀ + j * (8 * H) < φ x ∧ φ x ≤ X₀ + j * (8 * H) + 7 * H)
    (hsu : ∀ j < J, su j ≤ m) (hsv : ∀ j < J, sv j ≤ m)
    (ia : ∀ j < J, ∀ i < m, ∀ i' < m, a j i = a j i' → i = i')
    (ib : ∀ j < J, ∀ i < m, ∀ i' < m, b j i = b j i' → i = i')
    (hab : ∀ j < J, ∀ i < m, ∀ i' < m, a j i ≠ b j i') :
    (packetSet J su sv a b).card = ∑ j ∈ range J, (su j + sv j) := by
  unfold packetSet
  rw [card_biUnion (pairwiseDisjoint_blockSet φ hH hpos)]
  apply sum_congr rfl
  intro j hj
  have hj' := mem_range.mp hj
  exact card_blockSet (hsu j hj') (hsv j hj') (ia j hj') (ib j hj') (hab j hj')

theorem sum_packetSet (f : ℕ → ℝ) (φ : ℕ → ℝ) {J m : ℕ} {su sv : ℕ → ℕ} {a b : ℕ → ℕ → ℕ}
    {X₀ H : ℝ} (hH : 0 < H)
    (hpos : ∀ j < J, ∀ x ∈ blockSet su sv a b j,
      X₀ + j * (8 * H) < φ x ∧ φ x ≤ X₀ + j * (8 * H) + 7 * H)
    (hsu : ∀ j < J, su j ≤ m) (hsv : ∀ j < J, sv j ≤ m)
    (ia : ∀ j < J, ∀ i < m, ∀ i' < m, a j i = a j i' → i = i')
    (ib : ∀ j < J, ∀ i < m, ∀ i' < m, b j i = b j i' → i = i')
    (hab : ∀ j < J, ∀ i < m, ∀ i' < m, a j i ≠ b j i') :
    ∑ x ∈ packetSet J su sv a b, f x =
      ∑ j ∈ range J, (∑ i ∈ range (su j), f (a j i) + ∑ i ∈ range (sv j), f (b j i)) := by
  unfold packetSet
  rw [sum_biUnion (pairwiseDisjoint_blockSet φ hH hpos)]
  apply sum_congr rfl
  intro j hj
  have hj' := mem_range.mp hj
  exact sum_blockSet f (hsu j hj') (hsv j hj') (ia j hj') (ib j hj') (hab j hj')

theorem packetSet_pos (φ : ℕ → ℝ) {J : ℕ} {su sv : ℕ → ℕ} {a b : ℕ → ℕ → ℕ} {X₀ X₁ H : ℝ}
    (hH : 0 < H) (hJ : X₀ + J * (8 * H) ≤ X₁)
    (hpos : ∀ j < J, ∀ x ∈ blockSet su sv a b j,
      X₀ + j * (8 * H) < φ x ∧ φ x ≤ X₀ + j * (8 * H) + 7 * H) :
    ∀ x ∈ packetSet J su sv a b, X₀ < φ x ∧ φ x < X₁ := by
  intro x hx
  obtain ⟨j, hj, hxj⟩ := mem_biUnion.mp hx
  have hj' := mem_range.mp hj
  have h := hpos j hj' x hxj
  have hj0 : (0 : ℝ) ≤ j * (8 * H) := by positivity
  have hjJ : ((j : ℝ) + 1) * (8 * H) ≤ J * (8 * H) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hj') (by positivity)
  constructor <;> linarith [h.1, h.2]

theorem packetSet_prime {J m : ℕ} {su sv : ℕ → ℕ} {a b : ℕ → ℕ → ℕ}
    (hsu : ∀ j < J, su j ≤ m) (hsv : ∀ j < J, sv j ≤ m)
    (ha : ∀ j < J, ∀ i < m, (a j i).Prime) (hb : ∀ j < J, ∀ i < m, (b j i).Prime) :
    ∀ x ∈ packetSet J su sv a b, x.Prime := by
  intro x hx
  obtain ⟨j, hj, hxj⟩ := mem_biUnion.mp hx
  have hj' := mem_range.mp hj
  rcases mem_blockSet.mp hxj with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · exact ha j hj' i (by have := hsu j hj'; omega)
  · exact hb j hj' i (by have := hsv j hj'; omega)

/-- `X X^{-e} ≤ R R^{-e}` and `X^{-e} ≤ R^{-e}` for `0 < R ≤ X`, `e ≥ 1`. -/
theorem rpow_inv_antitone {R X e : ℝ} (hR : 0 < R) (hRX : R ≤ X) (he : 1 ≤ e) :
    X * (X ^ e)⁻¹ ≤ R * (R ^ e)⁻¹ ∧ (X ^ e)⁻¹ ≤ (R ^ e)⁻¹ := by
  have hX : 0 < X := hR.trans_le hRX
  have h2 : (X ^ e)⁻¹ ≤ (R ^ e)⁻¹ :=
    inv_anti₀ (Real.rpow_pos_of_pos hR _) (Real.rpow_le_rpow hR.le hRX (by linarith))
  refine ⟨?_, h2⟩
  have e1 : X * (X ^ e)⁻¹ = X ^ (1 - e) := by
    rw [Real.rpow_sub hX, Real.rpow_one, div_eq_mul_inv]
  have e2 : R * (R ^ e)⁻¹ = R ^ (1 - e) := by
    rw [Real.rpow_sub hR, Real.rpow_one, div_eq_mul_inv]
  rw [e1, e2]
  exact Real.rpow_le_rpow_of_nonpos hR hRX (by linarith)

/-! ### Scale bookkeeping -/

theorem four_rpow_supplyExp_le : (4 : ℝ) ^ supplyExp ≤ 4 := by
  calc (4 : ℝ) ^ supplyExp ≤ 4 ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) supplyExp_lt_one.le
    _ = 4 := Real.rpow_one 4

theorem cofactor_H_eq {q : ℕ} (hq : 1 ≤ q) {R : ℝ} (hR : 0 ≤ R) :
    (q : ℝ) * (4 * R / q) ^ supplyExp = 4 ^ supplyExp * (q * (R / q) ^ supplyExp) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [show 4 * R / q = 4 * (R / q) by ring, Real.mul_rpow (by norm_num) (by positivity)]
  ring

/-- Large-`R` thresholds for the cofactor construction. -/
theorem exists_cofactor_threshold (z₀ : ℝ) :
    ∃ R₀ : ℝ, 5 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      z₀ ^ 2 ≤ R ∧ 32 ≤ R ^ ((1 - supplyExp) / 2) ∧
        131072 * Real.log R ≤ R ^ (supplyExp / 2) ∧ 1 ≤ Real.log R := by
  have h1 : ∀ᶠ R : ℝ in atTop, 32 ≤ R ^ ((1 - supplyExp) / 2) :=
    (tendsto_rpow_atTop (by have := supplyExp_lt_one; linarith)).eventually_ge_atTop 32
  have h2 : ∀ᶠ R : ℝ in atTop, 131072 * Real.log R ≤ R ^ (supplyExp / 2) := by
    have ho := (isLittleO_log_rpow_atTop (by have := supplyExp_pos; linarith :
      (0 : ℝ) < supplyExp / 2)).def (c := 1 / 131072) (by norm_num)
    filter_upwards [ho, eventually_ge_atTop (1 : ℝ)] with R hR hR1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hR1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hR
    linarith
  have h3 : ∀ᶠ R : ℝ in atTop, 1 ≤ Real.log R :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  obtain ⟨X, hX⟩ := eventually_atTop.mp (((h1.and h2).and h3).and (eventually_ge_atTop (z₀ ^ 2)))
  refine ⟨max 5 X, le_max_left _ _, fun R hR => ?_⟩
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := hX R (le_of_max_le_right hR)
  exact ⟨d, a, b, c⟩

/-- The scale facts for a cofactor `1 ≤ q ≤ √R`. -/
theorem cofactor_scale_facts {R : ℝ} {q : ℕ} (hq : 1 ≤ q) (hqR : (q : ℝ) ^ 2 ≤ R) (hR : 1 ≤ R)
    (h32 : 32 ≤ R ^ ((1 - supplyExp) / 2)) :
    R ^ ((1 : ℝ) / 2) ≤ R / q ∧ R ^ (supplyExp / 2) ≤ (R / q) ^ supplyExp ∧
      8 * ((q : ℝ) * (4 * R / q) ^ supplyExp) ≤ R := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hR0 : 0 < R := by linarith
  have hqs : (q : ℝ) ≤ R ^ ((1 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow (by positivity) hqR (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hq0.le, show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num,
      Real.rpow_one] at h
  have hs0 : 0 < R ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hR0 _
  have hRq : R ^ ((1 : ℝ) / 2) ≤ R / q := by
    rw [le_div_iff₀ hq0]
    calc R ^ ((1 : ℝ) / 2) * q ≤ R ^ ((1 : ℝ) / 2) * R ^ ((1 : ℝ) / 2) := by gcongr
      _ = R := by rw [← Real.rpow_add hR0]; norm_num
  have hRqα : R ^ (supplyExp / 2) ≤ (R / q) ^ supplyExp := by
    calc R ^ (supplyExp / 2) = (R ^ ((1 : ℝ) / 2)) ^ supplyExp := by
          rw [← Real.rpow_mul hR0.le]; ring_nf
      _ ≤ _ := Real.rpow_le_rpow hs0.le hRq supplyExp_pos.le
  refine ⟨hRq, hRqα, ?_⟩
  -- `q (R/q)^α = q^{1-α} R^α ≤ R^{(1+α)/2}`
  have hqα : (q : ℝ) * (R / q) ^ supplyExp = q ^ (1 - supplyExp) * R ^ supplyExp := by
    rw [Real.div_rpow hR0.le hq0.le, Real.rpow_sub hq0, Real.rpow_one]
    field_simp
  have hq1α : (q : ℝ) ^ (1 - supplyExp) ≤ R ^ ((1 - supplyExp) / 2) := by
    calc (q : ℝ) ^ (1 - supplyExp) ≤ (R ^ ((1 : ℝ) / 2)) ^ (1 - supplyExp) :=
          Real.rpow_le_rpow hq0.le hqs (by have := supplyExp_lt_one; linarith)
      _ = R ^ ((1 - supplyExp) / 2) := by rw [← Real.rpow_mul hR0.le]; ring_nf
  have hsplit : R = R ^ ((1 - supplyExp) / 2) * R ^ ((1 + supplyExp) / 2) := by
    rw [← Real.rpow_add hR0, show (1 - supplyExp) / 2 + (1 + supplyExp) / 2 = (1 : ℝ) by ring,
      Real.rpow_one]
  have hRa : R ^ ((1 - supplyExp) / 2) * R ^ supplyExp = R ^ ((1 + supplyExp) / 2) := by
    rw [← Real.rpow_add hR0]; ring_nf
  rw [cofactor_H_eq hq hR0.le, hqα]
  have h4 := four_rpow_supplyExp_le
  have hp : 0 ≤ R ^ ((1 + supplyExp) / 2) := Real.rpow_nonneg hR0.le _
  have hRα : 0 ≤ R ^ supplyExp := Real.rpow_nonneg hR0.le _
  calc 8 * ((4 : ℝ) ^ supplyExp * ((q : ℝ) ^ (1 - supplyExp) * R ^ supplyExp))
      ≤ 8 * (4 * (R ^ ((1 - supplyExp) / 2) * R ^ supplyExp)) := by
        gcongr
    _ = 32 * R ^ ((1 + supplyExp) / 2) := by rw [hRa]; ring
    _ ≤ R ^ ((1 - supplyExp) / 2) * R ^ ((1 + supplyExp) / 2) := by gcongr
    _ = R := hsplit.symm

/-- `m L ≤ R^{2α} q^{1-2α} / (1024 log R)`. -/
theorem cofactor_mL_le {R : ℝ} {q m : ℕ} (hq : 1 ≤ q) (hR : 5 ≤ R)
    (hm : (m : ℝ) ≤ (R / q) ^ supplyExp / (32768 * Real.log (5 * R))) :
    (m : ℝ) * (8 * ((q : ℝ) * (4 * R / q) ^ supplyExp)) ≤
      R ^ (2 * supplyExp) * (q : ℝ) ^ (1 - 2 * supplyExp) / (1024 * Real.log R) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hR0 : 0 < R := by linarith
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
  have hlog5 : Real.log R ≤ Real.log (5 * R) := Real.log_le_log hR0 (by linarith)
  have hRq : 0 < R / q := by positivity
  have hkey : (R / q) ^ supplyExp * ((q : ℝ) * (R / q) ^ supplyExp) =
      R ^ (2 * supplyExp) * (q : ℝ) ^ (1 - 2 * supplyExp) := by
    rw [Real.div_rpow hR0.le hq0.le, Real.rpow_sub hq0, Real.rpow_one, show 2 * supplyExp =
      supplyExp + supplyExp by ring, Real.rpow_add hR0, Real.rpow_add hq0]
    field_simp
  rw [cofactor_H_eq hq hR0.le]
  have hα := four_rpow_supplyExp_le
  have hα0 : 0 ≤ (4 : ℝ) ^ supplyExp := Real.rpow_nonneg (by norm_num) _
  have hP : 0 ≤ (q : ℝ) * (R / q) ^ supplyExp := by positivity
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hl5 : 0 < Real.log (5 * R) := Real.log_pos (by linarith)
  have hx0 : 0 ≤ (R / q) ^ supplyExp / (32768 * Real.log (5 * R)) := by
    have := Real.rpow_nonneg hRq.le supplyExp
    positivity
  calc (m : ℝ) * (8 * (4 ^ supplyExp * ((q : ℝ) * (R / q) ^ supplyExp)))
      ≤ (R / q) ^ supplyExp / (32768 * Real.log (5 * R)) *
          (8 * (4 * ((q : ℝ) * (R / q) ^ supplyExp))) := by gcongr
    _ = 32 * ((R / q) ^ supplyExp * ((q : ℝ) * (R / q) ^ supplyExp)) /
          (32768 * Real.log (5 * R)) := by ring
    _ ≤ 32 * ((R / q) ^ supplyExp * ((q : ℝ) * (R / q) ^ supplyExp)) /
          (32768 * Real.log R) := by
        gcongr
    _ = _ := by rw [hkey]; ring

/-- `J m ≥ R / (2^22 q log R)` when `J ≥ R/L` and `m ≥ (R/q)^α/(65536 log 5R)`. -/
theorem cofactor_count_ge {R : ℝ} {q J m : ℕ} (hq : 1 ≤ q) (hR : 5 ≤ R)
    (hJ : R / (8 * ((q : ℝ) * (4 * R / q) ^ supplyExp)) ≤ J)
    (hm : (R / q) ^ supplyExp / (65536 * Real.log (5 * R)) ≤ m) :
    2⁻¹ ^ 22 * R / (q * Real.log R) ≤ (J : ℝ) * m := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hR0 : 0 < R := by linarith
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
  have hlog5 : Real.log (5 * R) ≤ 2 * Real.log R := by
    rw [Real.log_mul (by norm_num) hR0.ne']
    have : Real.log 5 ≤ Real.log R := Real.log_le_log (by norm_num) hR
    linarith
  have hRqα : 0 < (R / q) ^ supplyExp := Real.rpow_pos_of_pos (by positivity) _
  have hα := four_rpow_supplyExp_le
  have hα0 : 0 < (4 : ℝ) ^ supplyExp := Real.rpow_pos_of_pos (by norm_num) _
  rw [cofactor_H_eq hq hR0.le] at hJ
  have hJ0 : 0 ≤ R / (8 * (4 ^ supplyExp * ((q : ℝ) * (R / q) ^ supplyExp))) := by positivity
  have hl5 : 0 < Real.log (5 * R) := Real.log_pos (by linarith)
  have hm0 : 0 ≤ (R / q) ^ supplyExp / (65536 * Real.log (5 * R)) := by positivity
  calc 2⁻¹ ^ 22 * R / (q * Real.log R)
      ≤ R / (8 * (4 ^ supplyExp * q) * (65536 * Real.log (5 * R))) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : 8 * (4 ^ supplyExp * (q : ℝ)) * (65536 * Real.log (5 * R)) ≤
            8 * (4 * q) * (65536 * (2 * Real.log R)) := by gcongr
        nlinarith [mul_pos hR0 (mul_pos hq0 hlogR)]
    _ = R / (8 * (4 ^ supplyExp * ((q : ℝ) * (R / q) ^ supplyExp))) *
          ((R / q) ^ supplyExp / (65536 * Real.log (5 * R))) := by
        field_simp
    _ ≤ (J : ℝ) * m := mul_le_mul hJ hm hm0 (Nat.cast_nonneg J)

theorem block_bound_mono {A B X R e : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h1 : X * (X ^ e)⁻¹ ≤ R * (R ^ e)⁻¹) (h2 : (X ^ e)⁻¹ ≤ (R ^ e)⁻¹) :
    A * X * (X ^ e)⁻¹ + B * (X ^ e)⁻¹ ≤ A * R * (R ^ e)⁻¹ + B * (R ^ e)⁻¹ := by
  have e1 : A * X * (X ^ e)⁻¹ = A * (X * (X ^ e)⁻¹) := by ring
  have e2 : A * R * (R ^ e)⁻¹ = A * (R * (R ^ e)⁻¹) := by ring
  rw [e1, e2]
  exact add_le_add (mul_le_mul_of_nonneg_left h1 hA) (mul_le_mul_of_nonneg_left h2 hB)

/-- The final two-jet arithmetic for `J` blocks. -/
theorem cofactor_final_bound {R δ : ℝ} (hR : 1 ≤ R) {q J m : ℕ} (hq : 1 ≤ q)
    {L : ℝ} (hL : 0 ≤ L) (hJL : (J : ℝ) * L ≤ 2 * R)
    (hmL : (m : ℝ) * L ≤ R ^ (2 * supplyExp) * (q : ℝ) ^ (1 - 2 * supplyExp) / (1024 * Real.log R))
    (hlog : 0 < Real.log R) :
    (J : ℝ) * (jetConst 1 * L * R * (R ^ ((5 + δ) / 2))⁻¹ +
        8 * m * L ^ 2 * jetConst 2 * (R ^ ((5 + δ) / 2))⁻¹) ≤
      (2 * jetConst 1 + jetConst 2 + 1) * (R ^ (-(1 + δ) / 2) +
        R ^ (-(2 / 25 : ℝ) - δ / 2) * (q : ℝ) ^ (-(21 / 50 : ℝ)) / Real.log R) := by
  have hR0 : 0 < R := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have he : 0 < R ^ ((5 + δ) / 2) := Real.rpow_pos_of_pos hR0 _
  have hj1 := jetConst_nonneg 1
  have hj2 := jetConst_nonneg 2
  have hinv : 0 ≤ (R ^ ((5 + δ) / 2))⁻¹ := (inv_pos.mpr he).le
  have hid1 : R * R * (R ^ ((5 + δ) / 2))⁻¹ = R ^ (-(1 + δ) / 2) := by
    rw [← Real.rpow_neg hR0.le, show R * R * R ^ (-((5 + δ) / 2)) =
      R ^ (1 : ℝ) * R ^ (1 : ℝ) * R ^ (-((5 + δ) / 2)) by rw [Real.rpow_one],
      ← Real.rpow_add hR0, ← Real.rpow_add hR0]
    congr 1; ring
  have hid2 : R ^ (2 * supplyExp) * R * (R ^ ((5 + δ) / 2))⁻¹ = R ^ (-(2 / 25 : ℝ) - δ / 2) := by
    rw [← Real.rpow_neg hR0.le, show R ^ (2 * supplyExp) * R * R ^ (-((5 + δ) / 2)) =
      R ^ (2 * supplyExp) * R ^ (1 : ℝ) * R ^ (-((5 + δ) / 2)) by rw [Real.rpow_one],
      ← Real.rpow_add hR0, ← Real.rpow_add hR0]
    congr 1; norm_num [supplyExp]; ring
  have hq21 : (q : ℝ) ^ (1 - 2 * supplyExp) = (q : ℝ) ^ (-(21 / 50 : ℝ)) := by
    congr 1; norm_num [supplyExp]
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hA : (J : ℝ) * (jetConst 1 * L * R * (R ^ ((5 + δ) / 2))⁻¹) ≤
      2 * jetConst 1 * R ^ (-(1 + δ) / 2) := by
    rw [← hid1]
    have : (J : ℝ) * (jetConst 1 * L * R * (R ^ ((5 + δ) / 2))⁻¹) =
        jetConst 1 * (J * L) * R * (R ^ ((5 + δ) / 2))⁻¹ := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hJL hj1
    calc jetConst 1 * (J * L) * R * (R ^ ((5 + δ) / 2))⁻¹
        ≤ jetConst 1 * (2 * R) * R * (R ^ ((5 + δ) / 2))⁻¹ := by gcongr
      _ = _ := by ring
  have hB : (J : ℝ) * (8 * m * L ^ 2 * jetConst 2 * (R ^ ((5 + δ) / 2))⁻¹) ≤
      jetConst 2 * (R ^ (-(2 / 25 : ℝ) - δ / 2) * (q : ℝ) ^ (-(21 / 50 : ℝ)) / Real.log R) := by
    rw [← hid2, ← hq21]
    have e : (J : ℝ) * (8 * m * L ^ 2 * jetConst 2 * (R ^ ((5 + δ) / 2))⁻¹) =
        8 * jetConst 2 * ((J * L) * (m * L)) * (R ^ ((5 + δ) / 2))⁻¹ := by ring
    rw [e]
    have hmL0 : 0 ≤ (m : ℝ) * L := mul_nonneg hm0 hL
    have hprod : (J * L) * (m * L) ≤ (2 * R) *
        (R ^ (2 * supplyExp) * (q : ℝ) ^ (1 - 2 * supplyExp) / (1024 * Real.log R)) :=
      mul_le_mul hJL hmL hmL0 (by linarith)
    calc 8 * jetConst 2 * ((J * L) * (m * L)) * (R ^ ((5 + δ) / 2))⁻¹
        ≤ 8 * jetConst 2 * ((2 * R) *
            (R ^ (2 * supplyExp) * (q : ℝ) ^ (1 - 2 * supplyExp) / (1024 * Real.log R))) *
              (R ^ ((5 + δ) / 2))⁻¹ := by gcongr
      _ = jetConst 2 / 64 * (R ^ (2 * supplyExp) * R * (R ^ ((5 + δ) / 2))⁻¹ *
            (q : ℝ) ^ (1 - 2 * supplyExp) / Real.log R) := by
          field_simp
          ring
      _ ≤ jetConst 2 * (R ^ (2 * supplyExp) * R * (R ^ ((5 + δ) / 2))⁻¹ *
            (q : ℝ) ^ (1 - 2 * supplyExp) / Real.log R) := by
          have : 0 ≤ R ^ (2 * supplyExp) * R * (R ^ ((5 + δ) / 2))⁻¹ *
              (q : ℝ) ^ (1 - 2 * supplyExp) / Real.log R := by
            have := Real.rpow_nonneg hR0.le (2 * supplyExp)
            have := Real.rpow_nonneg hq0.le (1 - 2 * supplyExp)
            positivity
          nlinarith
  have hP1 : 0 ≤ R ^ (-(1 + δ) / 2) := Real.rpow_nonneg hR0.le _
  have hP2 : 0 ≤ R ^ (-(2 / 25 : ℝ) - δ / 2) * (q : ℝ) ^ (-(21 / 50 : ℝ)) / Real.log R := by
    have := Real.rpow_nonneg hR0.le (-(2 / 25 : ℝ) - δ / 2)
    have := Real.rpow_nonneg hq0.le (-(21 / 50 : ℝ))
    positivity
  rw [mul_add]
  nlinarith

/-! ### The cofactor packet (8) -/

/-- **Balanced cofactor two-jet packet (8).**  For all large `R`, every cofactor `1 ≤ q ≤ √R`
admits primes `r` with `R < qr < 2R` and `p` with `2R < qp < 4R`, equally many and at least
`c R/(q log R)` of each, such that uniformly in `0 ≤ δ ≤ 1`
`‖Σ_r f_{2qr} - Σ_p f_{qp}‖_δ ≤ C [R^{-(1+δ)/2} + R^{-2/25-δ/2} q^{-21/50} / log R]`. -/
theorem exists_cofactor_two_jet_packet :
    ∃ R₀ C c : ℝ, 5 ≤ R₀ ∧ 0 < C ∧ 0 < c ∧ ∀ R : ℝ, R₀ ≤ R → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ^ 2 ≤ R →
      ∃ Rs Ps : Finset ℕ,
        (∀ r ∈ Rs, r.Prime ∧ R < ((q * r : ℕ) : ℝ) ∧ ((q * r : ℕ) : ℝ) < 2 * R) ∧
        (∀ p ∈ Ps, p.Prime ∧ 2 * R < ((q * p : ℕ) : ℝ) ∧ ((q * p : ℕ) : ℝ) < 4 * R) ∧
        Rs.card = Ps.card ∧ c * R / (q * Real.log R) ≤ Rs.card ∧
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
          gammaNorm δ (fun t => ∑ r ∈ Rs, atom ((2 * q * r : ℕ) : ℝ) t -
            ∑ p ∈ Ps, atom ((q * p : ℕ) : ℝ) t) ≤
            C * (R ^ (-(1 + δ) / 2) +
              R ^ (-(2 / 25 : ℝ) - δ / 2) * (q : ℝ) ^ (-(21 / 50 : ℝ)) / Real.log R) := by
  obtain ⟨z₀, hz₀, hsupply⟩ := exists_theta_window_supply
  obtain ⟨R₀, hR₀, hthr⟩ := exists_cofactor_threshold z₀
  have hC : 0 < 2 * jetConst 1 + jetConst 2 + 1 := by
    have := jetConst_nonneg 1; have := jetConst_nonneg 2; linarith
  refine ⟨R₀, 2 * jetConst 1 + jetConst 2 + 1, 2⁻¹ ^ 22, hR₀, hC, by positivity,
    fun R hR q hq hqR => ?_⟩
  obtain ⟨hz0R, h32, hlogR, hlog1⟩ := hthr R hR
  have hR5 : 5 ≤ R := hR₀.trans hR
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨hsq, hRqα, hLR⟩ := cofactor_scale_facts hq hqR hR1 h32
  have hlogpos : 0 < Real.log R := by linarith
  have hlog5 : 0 < Real.log (5 * R) := Real.log_pos (by linarith)
  have hlog52 : Real.log (5 * R) ≤ 2 * Real.log R := by
    rw [Real.log_mul (by norm_num) hR0.ne']
    have : Real.log 5 ≤ Real.log R := Real.log_le_log (by norm_num) hR5
    linarith
  -- `z₀ ≤ R/q`
  have hRq : z₀ ≤ R / q := by
    have hz : z₀ ≤ R ^ ((1 : ℝ) / 2) := by
      rcases le_or_gt z₀ 0 with h | h
      · exact h.trans (Real.rpow_nonneg hR0.le _)
      · have := Real.rpow_le_rpow (by positivity) hz0R (by norm_num : (0 : ℝ) ≤ 1 / 2)
        rwa [← Real.rpow_natCast, ← Real.rpow_mul h.le,
          show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] at this
    exact hz.trans hsq
  set H : ℝ := q * (4 * R / q) ^ supplyExp with hHdef
  have hH0 : 0 < H := by
    rw [hHdef]
    have := Real.rpow_pos_of_pos (by positivity : 0 < 4 * R / q) supplyExp
    positivity
  set J : ℕ := ⌊2 * R / (8 * H)⌋₊ with hJdef
  set m : ℕ := ⌊(R / q) ^ supplyExp / (32768 * Real.log (5 * R))⌋₊ with hmdef
  have hmle : (m : ℝ) ≤ (R / q) ^ supplyExp / (32768 * Real.log (5 * R)) :=
    Nat.floor_le (by have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ R / q) supplyExp; positivity)
  have hmle' : (m : ℝ) ≤ (R / q) ^ supplyExp / (16384 * Real.log (5 * R)) := by
    refine hmle.trans ?_
    have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ R / q) supplyExp
    gcongr
    norm_num
  have hJL : (J : ℝ) * (8 * H) ≤ 2 * R := by
    have h := Nat.floor_le (show 0 ≤ 2 * R / (8 * H) by positivity)
    rw [← hJdef] at h
    calc (J : ℝ) * (8 * H) ≤ 2 * R / (8 * H) * (8 * H) := by gcongr
      _ = 2 * R := by field_simp
  -- one block for each `j < J`
  have hblock : ∀ j : ℕ, j < J → ∃ rN rP pN pP : ℕ → ℕ, ∃ su sv : ℕ, su ≤ m ∧ sv ≤ m ∧
      (su = m ∨ sv = m) ∧
      (∀ i < m, (rN i).Prime ∧ 2 * R + j * (8 * H) < ((2 * q * rN i : ℕ) : ℝ) ∧
        ((2 * q * rN i : ℕ) : ℝ) ≤ 2 * R + j * (8 * H) + H) ∧
      (∀ i < m, (rP i).Prime ∧ 2 * R + j * (8 * H) + 6 * H < ((2 * q * rP i : ℕ) : ℝ) ∧
        ((2 * q * rP i : ℕ) : ℝ) ≤ 2 * R + j * (8 * H) + 7 * H) ∧
      (∀ i < m, (pN i).Prime ∧ 2 * R + j * (8 * H) < ((q * pN i : ℕ) : ℝ) ∧
        ((q * pN i : ℕ) : ℝ) ≤ 2 * R + j * (8 * H) + H) ∧
      (∀ i < m, (pP i).Prime ∧ 2 * R + j * (8 * H) + 6 * H < ((q * pP i : ℕ) : ℝ) ∧
        ((q * pP i : ℕ) : ℝ) ≤ 2 * R + j * (8 * H) + 7 * H) ∧
      (∀ i < m, ∀ i' < m, rN i = rN i' → i = i') ∧ (∀ i < m, ∀ i' < m, rP i = rP i' → i = i') ∧
      (∀ i < m, ∀ i' < m, pN i = pN i' → i = i') ∧ (∀ i < m, ∀ i' < m, pP i = pP i' → i = i') ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        gammaNorm δ (fun t => ∑ i ∈ range su,
            (atom ((2 * q * rN i : ℕ) : ℝ) t - atom ((q * pP i : ℕ) : ℝ) t) +
          ∑ i ∈ range sv, (atom ((2 * q * rP i : ℕ) : ℝ) t - atom ((q * pN i : ℕ) : ℝ) t)) ≤
          jetConst 1 * (8 * H) * (2 * R + j * (8 * H)) *
              ((2 * R + j * (8 * H)) ^ ((5 + δ) / 2))⁻¹ +
            8 * m * (8 * H) ^ 2 * jetConst 2 * ((2 * R + j * (8 * H)) ^ ((5 + δ) / 2))⁻¹ := by
    intro j hj
    have hjJ : (j : ℝ) + 1 ≤ J := by exact_mod_cast hj
    have hXL : 2 * R + j * (8 * H) + 8 * H ≤ 4 * R := by nlinarith
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    exact exists_cofactor_block hz₀ hsupply hR1 hq hRq (by nlinarith) hXL (by nlinarith) m hmle'
  choose! rN rP pN pP su sv hsu hsv hend hrN hrP hpN hpP irN irP ipN ipP hb using hblock
  -- the two atom sets
  have hposR : ∀ j < J, ∀ x ∈ blockSet su sv rN rP j,
      2 * R + j * (8 * H) < ((2 * q * x : ℕ) : ℝ) ∧
        ((2 * q * x : ℕ) : ℝ) ≤ 2 * R + j * (8 * H) + 7 * H := by
    intro j hj x hx
    rcases mem_blockSet.mp hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · have h := hrN j hj i (by have := hsu j hj; omega)
      exact ⟨h.2.1, by linarith [h.2.2]⟩
    · have h := hrP j hj i (by have := hsv j hj; omega)
      exact ⟨by linarith [h.2.1], h.2.2⟩
  have hposP : ∀ j < J, ∀ x ∈ blockSet su sv pP pN j,
      2 * R + j * (8 * H) < ((q * x : ℕ) : ℝ) ∧
        ((q * x : ℕ) : ℝ) ≤ 2 * R + j * (8 * H) + 7 * H := by
    intro j hj x hx
    rcases mem_blockSet.mp hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · have h := hpP j hj i (by have := hsu j hj; omega)
      exact ⟨by linarith [h.2.1], h.2.2⟩
    · have h := hpN j hj i (by have := hsv j hj; omega)
      exact ⟨h.2.1, by linarith [h.2.2]⟩
  have habR : ∀ j < J, ∀ i < m, ∀ i' < m, rN j i ≠ rP j i' := by
    intro j hj i hi i' hi' he
    have h1 := hrN j hj i hi
    have h2 := hrP j hj i' hi'
    rw [he] at h1
    linarith [h1.2.2, h2.2.1]
  have habP : ∀ j < J, ∀ i < m, ∀ i' < m, pP j i ≠ pN j i' := by
    intro j hj i hi i' hi' he
    have h1 := hpP j hj i hi
    have h2 := hpN j hj i' hi'
    rw [he] at h1
    linarith [h1.2.1, h2.2.2]
  have hcardR := card_packetSet (fun x => ((2 * q * x : ℕ) : ℝ)) hH0 hposR hsu hsv irN irP habR
  have hcardP := card_packetSet (fun x => ((q * x : ℕ) : ℝ)) hH0 hposP hsu hsv ipP ipN habP
  have hJX : 2 * R + J * (8 * H) ≤ 4 * R := by linarith
  have hRpos := packetSet_pos (fun x => ((2 * q * x : ℕ) : ℝ)) hH0 hJX hposR
  have hPpos := packetSet_pos (fun x => ((q * x : ℕ) : ℝ)) hH0 hJX hposP
  have hRpr := packetSet_prime hsu hsv (fun j hj i hi => (hrN j hj i hi).1)
    (fun j hj i hi => (hrP j hj i hi).1)
  have hPpr := packetSet_prime hsu hsv (fun j hj i hi => (hpP j hj i hi).1)
    (fun j hj i hi => (hpN j hj i hi).1)
  refine ⟨packetSet J su sv rN rP, packetSet J su sv pP pN, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    have h := hRpos r hr
    have e : ((2 * q * r : ℕ) : ℝ) = 2 * ((q * r : ℕ) : ℝ) := by push_cast; ring
    rw [e] at h
    exact ⟨hRpr r hr, by linarith [h.1], by linarith [h.2]⟩
  · intro p hp
    exact ⟨hPpr p hp, (hPpos p hp).1, (hPpos p hp).2⟩
  · rw [hcardR, hcardP]
  · -- the count
    rw [hcardR]
    have hsum : (J : ℝ) * m ≤ ((∑ j ∈ range J, (su j + sv j) : ℕ) : ℝ) := by
      have : J * m ≤ ∑ j ∈ range J, (su j + sv j) := by
        calc J * m = ∑ _j ∈ range J, m := by rw [sum_const, card_range, smul_eq_mul]
          _ ≤ _ := by
              apply sum_le_sum
              intro j hj
              rcases hend j (mem_range.mp hj) with h | h <;> omega
      exact_mod_cast this
    refine le_trans ?_ hsum
    apply cofactor_count_ge hq hR5
    · -- `J ≥ R/L`
      have h := Nat.lt_floor_add_one (2 * R / (8 * H))
      rw [← hJdef] at h
      have hRL : 1 ≤ R / (8 * H) := by rw [le_div_iff₀ (by positivity)]; linarith
      have : 2 * R / (8 * H) = 2 * (R / (8 * H)) := by ring
      show R / (8 * H) ≤ (J : ℝ)
      linarith
    · -- `m ≥ (R/q)^α/(65536 log 5R)`
      have h := Nat.lt_floor_add_one ((R / q) ^ supplyExp / (32768 * Real.log (5 * R)))
      rw [← hmdef] at h
      have h2 : 2 ≤ (R / q) ^ supplyExp / (32768 * Real.log (5 * R)) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      have e : (R / q) ^ supplyExp / (65536 * Real.log (5 * R)) =
          (R / q) ^ supplyExp / (32768 * Real.log (5 * R)) / 2 := by
        field_simp; ring
      rw [e]
      linarith
  · -- the norm
    intro δ hδ0 hδ1
    have hδ : 0 < 5 + δ := by linarith
    set G : ℕ → ℝ → ℝ := fun j t => ∑ i ∈ range (su j),
        (atom ((2 * q * rN j i : ℕ) : ℝ) t - atom ((q * pP j i : ℕ) : ℝ) t) +
      ∑ i ∈ range (sv j), (atom ((2 * q * rP j i : ℕ) : ℝ) t - atom ((q * pN j i : ℕ) : ℝ) t)
      with hG
    have hfun : (fun t => ∑ r ∈ packetSet J su sv rN rP, atom ((2 * q * r : ℕ) : ℝ) t -
        ∑ p ∈ packetSet J su sv pP pN, atom ((q * p : ℕ) : ℝ) t) =
        fun t => ∑ j ∈ range J, G j t := by
      funext t
      rw [sum_packetSet (fun r => atom ((2 * q * r : ℕ) : ℝ) t) (fun x => ((2 * q * x : ℕ) : ℝ))
          hH0 hposR hsu hsv irN irP habR,
        sum_packetSet (fun p => atom ((q * p : ℕ) : ℝ) t) (fun x => ((q * x : ℕ) : ℝ))
          hH0 hposP hsu hsv ipP ipN habP, ← sum_sub_distrib]
      apply sum_congr rfl
      intro j _
      simp only [hG, sum_sub_distrib]
      ring
    have hfin : ∀ j ∈ range J, GammaFinite δ (G j) := by
      intro j hj
      have hj' := mem_range.mp hj
      refine (GammaFinite.sum _ fun i hi => ?_).add (GammaFinite.sum _ fun i hi => ?_)
      · have hi' : i < m := by have := mem_range.mp hi; have := hsu j hj'; omega
        exact (gammaFinite_atom hδ (Nat.cast_pos.mpr (Nat.mul_pos (Nat.mul_pos two_pos hq)
          (hrN j hj' i hi').1.pos))).sub
          (gammaFinite_atom hδ (Nat.cast_pos.mpr (Nat.mul_pos hq (hpP j hj' i hi').1.pos)))
      · have hi' : i < m := by have := mem_range.mp hi; have := hsv j hj'; omega
        exact (gammaFinite_atom hδ (Nat.cast_pos.mpr (Nat.mul_pos (Nat.mul_pos two_pos hq)
          (hrP j hj' i hi').1.pos))).sub
          (gammaFinite_atom hδ (Nat.cast_pos.mpr (Nat.mul_pos hq (hpN j hj' i hi').1.pos)))
    rw [hfun]
    refine (gammaNorm_sum_le hδ _ hfin).trans ?_
    have hblockR : ∀ j ∈ range J, gammaNorm δ (G j) ≤
        jetConst 1 * (8 * H) * R * (R ^ ((5 + δ) / 2))⁻¹ +
          8 * m * (8 * H) ^ 2 * jetConst 2 * (R ^ ((5 + δ) / 2))⁻¹ := by
      intro j hj
      have hj' := mem_range.mp hj
      refine (hb j hj' δ hδ0 hδ1).trans ?_
      have hX : R ≤ 2 * R + j * (8 * H) := by
        have : (0 : ℝ) ≤ j * (8 * H) := by positivity
        linarith
      obtain ⟨h1, h2⟩ := rpow_inv_antitone hR0 hX (by linarith : (1 : ℝ) ≤ (5 + δ) / 2)
      exact block_bound_mono (by have := jetConst_nonneg 1; positivity)
        (by have := jetConst_nonneg 2; positivity) h1 h2
    refine (sum_le_sum hblockR).trans ?_
    rw [sum_const, card_range, nsmul_eq_mul]
    exact cofactor_final_bound hR1 hq (by positivity) hJL
      (cofactor_mL_le hq hR5 hmle) hlogpos

end RHTower.CubicGamma
