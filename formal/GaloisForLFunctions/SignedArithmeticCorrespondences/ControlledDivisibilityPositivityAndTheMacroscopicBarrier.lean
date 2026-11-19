import GaloisForLFunctions.SignedArithmeticCorrespondences.DivisorIncidenceOnLateCombs
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheRiemannHypothesisIsExactEventualCombPositivity
import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheFirstOverlapStepOfWeilsFormFailsForTheSignTwin
import GaloisForLFunctions.RHTower.Sieve.Mertens
import Mathlib.NumberTheory.Bertrand

/-!
# Controlled divisibility positivity and the macroscopic cost barrier

Establish the sharp boundary between universal divisibility-driven positivity on
late combs `S = Ioc N (N + 3KN)` and the Riemann Hypothesis:

1. **Controlled-cost positivity producer**: for every `K ≥ 1`, every contact weight
   `w : ℕ → ℝ`, and every `κ > 0`, there is `C > 0` such that eventually in `N`,
   every finite linear combination `c = ∑_{t ∈ T} α_t v_{d_t, r_t}` of centered
   congruence indicators satisfies
   `combFormW w S c ≥ κ ∑_{n ∈ S} c(n)^2 - (C / N) (∑_{t ∈ T} |α_t|)^2`.
2. **Complete solution of the two-prime pilot and `√N`-prime spans**: specializing to
   singletons and combining with the uniform `O_{K, w}(1 + log N)` mixed bilinear bound
   and Chinese Remainder Gram orthogonality proves `0 < A`, `0 < C`, and `B^2 ≤ A C`
   uniformly for all distinct primes `p, q ≤ c_2 √N`, and proves unconditional eventual
   positivity on the entire unrestricted real span of `{v_p : p ≤ C_0 √N}` for both
   `Λ` and `SelectiveArithmetic.liouvilleWeight`.
3. **Sharp macroscopic cost barrier, Liouville refutation, and RH equivalence**:
   Möbius upper-triangular inversion and Bertrand's postulate (`∑_{t=1}^Q μ(t)/t ≠ 0`)
   represent every `c : S → ℝ` as `∑_{d=2}^{(1+3K)N} α_d v_d` on `S` at macroscopic
   cost `(∑ |α_d|)^2 ≤ C_K^* N ∑_{n ∈ S} c(n)^2`. At this exact `N · ‖c‖_2^2` cost
   scale, `SelectiveArithmetic.liouvilleWeight` becomes strictly negative (`< -(1/2000) ‖c‖_2^2`)
   at every `K ≥ 1`, whereas paying `mixedPrimeDebit ≤ diagRealBudget` for `Λ` across
   macroscopic-cost divisibility combinations is unconditionally equivalent to
   `RiemannHypothesis`.
-/

noncomputable section

namespace GaloisForLFunctions.SignedArithmeticCorrespondences

open Finset Filter Topology
open HodgeTheoryOfAFixedPart
open AbsoluteGeometryOfSpecZ (jetKernel jetKernel_comm stepPacket packetForm stepEntry
  nestedCoeff stepPacket_eq_nested packetForm_nested_eq abs_half_sum_sum_le
  sum_nestedCoeff_sq_le sum_blockFunction_sq nested_bounds
  tendsto_combForm_blockFunction_div combForm_of_subset combForm_congr)
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

/-! ### Subset invariance and bounded-ratio Schur transfer for `combFormW` -/

theorem combFormW_congr (w : ℕ → ℝ) {S : Finset ℕ} {c e : ℕ → ℝ}
    (h : ∀ n ∈ S, c n = e n) : combFormW w S c = combFormW w S e := by
  have hd1 : degOne S c = degOne S e := sum_congr rfl fun n hn => by rw [h n hn]
  have hd2 : degTwo S c = degTwo S e := sum_congr rfl fun n hn => h n hn
  have hp : combPairingW w S c = combPairingW w S e := by
    unfold combPairingW
    congr 1
    · refine sum_congr rfl fun n hn => sum_congr rfl fun m hm => ?_
      rw [h m (mem_of_mem_erase hm), h n hn]
    · exact sum_congr rfl fun n hn => by rw [h n hn]
  rw [combFormW, combFormW, hd1, hd2, hp]

theorem combFormW_of_subset (w : ℕ → ℝ) {W S : Finset ℕ} {c : ℕ → ℝ}
    (hWS : W ⊆ S) (h0 : ∀ n ∈ S, n ∉ W → c n = 0) :
    combFormW w S c = combFormW w W c := by
  have h1 : combForm S c = combForm W c := combForm_of_subset hWS h0
  have h2 : ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * contactW (fun k => w k - Λ k) m n =
      ∑ n ∈ W, ∑ m ∈ W.erase n, c m * c n * contactW (fun k => w k - Λ k) m n := by
    have hout : ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * contactW (fun k => w k - Λ k) m n =
        ∑ n ∈ W, ∑ m ∈ S.erase n, c m * c n * contactW (fun k => w k - Λ k) m n :=
      (sum_subset hWS fun n hn hnW => sum_eq_zero fun m _ => by rw [h0 n hn hnW]; ring).symm
    have hin : ∀ n ∈ W,
        ∑ m ∈ S.erase n, c m * c n * contactW (fun k => w k - Λ k) m n =
          ∑ m ∈ W.erase n, c m * c n * contactW (fun k => w k - Λ k) m n := fun n _ =>
      (sum_subset (erase_subset_erase n hWS) fun m hm hmW => by
        have hmS : m ∈ S := mem_of_mem_erase hm
        have hmW' : m ∉ W := fun h => hmW (mem_erase.mpr ⟨(mem_erase.mp hm).1, h⟩)
        rw [h0 m hmS hmW']; ring).symm
    rw [hout, sum_congr rfl hin]
  rw [combFormW_eq, combFormW_eq, h1, h2]

/-- On `S = Ioc N (N + 3KN)`, every contact weight `u` defines a bounded quadratic
form of operator norm at most `2 ∑_{r=2}^{3K} |u(r)|`. -/
theorem abs_contactTerm_lateComb_self_le (u : ℕ → ℝ) (N K : ℕ) (c : ℕ → ℝ) :
    |contactTerm u (Ioc N (N + 3 * K * N)) c c| ≤
      (2 * ∑ r ∈ Icc 2 (3 * K), |u r|) * ∑ n ∈ Ioc N (N + 3 * K * N), c n ^ 2 := by
  set S := Ioc N (N + 3 * K * N)
  rw [contactTerm_lateComb_eq]
  have hslice (r : ℕ) (hr : r ∈ Icc 2 (3 * K)) :
      |∑ m ∈ combSlice N K r, (c m * c (r * m) + c (r * m) * c m)| ≤
        2 * ∑ n ∈ S, c n ^ 2 := by
    have hr0 : 0 < r := by have := (mem_Icc.mp hr).1; omega
    have hsub1 : combSlice N K r ⊆ S := by
      intro m hm
      obtain ⟨h1, h2⟩ := mem_Ioc.mp hm
      exact mem_Ioc.mpr ⟨h1, h2.trans (Nat.div_le_self _ _)⟩
    have hsub2 : (combSlice N K r).image (r * ·) ⊆ S := by
      intro n hn
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
      obtain ⟨h1, h2⟩ := mem_Ioc.mp hm
      have hr2 := (mem_Icc.mp hr).1
      exact mem_Ioc.mpr ⟨by nlinarith, by
        rw [mul_comm]; exact (Nat.le_div_iff_mul_le hr0).mp h2⟩
    have hinj : ∀ a ∈ combSlice N K r, ∀ b ∈ combSlice N K r, r * a = r * b → a = b :=
      fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hr0 hab
    calc |∑ m ∈ combSlice N K r, (c m * c (r * m) + c (r * m) * c m)|
        ≤ ∑ m ∈ combSlice N K r, |c m * c (r * m) + c (r * m) * c m| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ combSlice N K r, (c m ^ 2 + c (r * m) ^ 2) := by
          refine sum_le_sum fun m _ => ?_
          rw [show c m * c (r * m) + c (r * m) * c m = 2 * (c m * c (r * m)) by ring, abs_le]
          constructor <;> nlinarith [sq_nonneg (c m - c (r * m)), sq_nonneg (c m + c (r * m))]
      _ = (∑ m ∈ combSlice N K r, c m ^ 2) + ∑ m ∈ combSlice N K r, c (r * m) ^ 2 :=
          sum_add_distrib
      _ ≤ (∑ n ∈ S, c n ^ 2) + ∑ n ∈ S, c n ^ 2 := by
          refine add_le_add
            (sum_le_sum_of_subset_of_nonneg hsub1 fun _ _ _ => sq_nonneg _) ?_
          rw [← sum_image hinj]
          exact sum_le_sum_of_subset_of_nonneg hsub2 fun _ _ _ => sq_nonneg _
      _ = 2 * ∑ n ∈ S, c n ^ 2 := by ring
  calc |∑ r ∈ Icc 2 (3 * K), u r * ∑ m ∈ combSlice N K r, (c m * c (r * m) + c (r * m) * c m)|
      ≤ ∑ r ∈ Icc 2 (3 * K), |u r * ∑ m ∈ combSlice N K r, (c m * c (r * m) + c (r * m) * c m)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Icc 2 (3 * K), |u r| * (2 * ∑ n ∈ S, c n ^ 2) := by
        refine sum_le_sum fun r hr => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hslice r hr) (abs_nonneg _)
    _ = (2 * ∑ r ∈ Icc 2 (3 * K), |u r|) * ∑ n ∈ S, c n ^ 2 := by
        rw [← sum_mul]; ring

/-! ### General controlled-cost divisibility positivity producer -/

private theorem exists_abs_packetForm_stepPacket_le {Q R J : ℕ} (hR : 1 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ : ℕ → ℝ,
      |packetForm Q (stepPacket R J σ)| ≤ M * ∑ j ∈ range J, σ j ^ 2 := by
  let δ : ℝ := ∑ i ∈ range (J + 1), ∑ l ∈ range (J + 1), |stepEntry Q R (fun j => R + j) i l|
  have hδ0 : 0 ≤ δ := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨2 * δ * ((J + 1 : ℕ) : ℝ), by positivity, fun σ => ?_⟩
  have hbound : ∀ i ∈ range (J + 1), ∀ l ∈ range (J + 1),
      |stepEntry Q R (fun j => R + j) i l| ≤ δ := fun i hi l hl => by
    have h1 : |stepEntry Q R (fun j => R + j) i l| ≤
        ∑ l' ∈ range (J + 1), |stepEntry Q R (fun j => R + j) i l'| :=
      single_le_sum (fun _ _ => abs_nonneg _) hl
    exact h1.trans (single_le_sum (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) hi)
  rw [stepPacket_eq_nested hR J σ, packetForm_nested_eq hR (nested_bounds R J)]
  have hab := abs_half_sum_sum_le (s := range (J + 1)) (nestedCoeff J σ)
    (stepEntry Q R (fun j => R + j)) hbound
  rw [card_range] at hab
  have hsq := sum_nestedCoeff_sq_le J σ
  have hmul := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ δ / 2 * ((J + 1 : ℕ) : ℝ) by positivity)
  linarith

private theorem image_range_block_eq_Ioc (N₀ B j : ℕ) :
    (range B).image (fun a => N₀ + 1 + B * j + a) = Ioc (N₀ + B * j) (N₀ + B * j + B) := by
  ext n
  simp only [mem_image, mem_range, mem_Ioc]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨n - (N₀ + 1 + B * j), by omega, by omega⟩

/-- **Controlled-cost positivity producer.** For every comb width `K`, contact
weight `w`, and desired mass margin `κ > 0`, there is `C > 0` such that eventually
in `N`, every finite linear combination `c(n) = ∑_{t ∈ T} α_t v_{d_t, r_t}(n)` of
centered congruence indicators (`d_t ≥ 1`) satisfies
`combFormW w S c ≥ κ ∑_{n ∈ S} c(n)^2 - (C / N) (∑_{t ∈ T} |α_t|)^2`. -/
theorem eventually_combFormW_controlled_residue_ge (K : ℕ)
    (w : ℕ → ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ {ι : Type*} (T : Finset ι) (d r : ι → ℕ) (α : ι → ℝ),
        (∀ t ∈ T, 0 < d t) →
        let S := Ioc N (N + 3 * K * N)
        let c := fun n => ∑ t ∈ T, α t * centeredResidue (d t) (r t) n
        κ * ∑ n ∈ S, c n ^ 2 - C / (N : ℝ) * (∑ t ∈ T, |α t|) ^ 2 ≤ combFormW w S c := by
  set D_w : ℝ := 2 * ∑ r ∈ Icc 2 (3 * K), |w r - Λ r|
  have hDw : 0 ≤ D_w := by positivity
  set κ₀ : ℝ := κ + D_w
  have hκ₀ : 0 < κ₀ := by linarith
  set Q : ℕ := 6 * K + 2
  obtain ⟨R, hR, hred⟩ := exists_blockSize_combForm_ge_blockMean_with_residual Q zero_lt_one κ₀
  set J : ℕ := (6 * K + 1) * R
  have hR1 : 1 ≤ R := hR
  have hQ : R + J ≤ Q * R := by dsimp only [J, Q]; exact le_of_eq (by ring)
  obtain ⟨M_step, hM_step0, hM_step⟩ := exists_abs_packetForm_stepPacket_le (Q := Q) (J := J) hR1
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp
    (eventually_packetForm_stepPacket_le_combForm hR1 hQ zero_lt_one)
  set C : ℝ := 2 * (R : ℝ) * (J : ℝ) * (M_step + κ₀ + 3) + 1
  have hC : 0 < C := by positivity
  refine ⟨C, hC, eventually_atTop.mpr ⟨R * (B₀ + 2), fun N hN => ?_⟩⟩
  intro ι T d r α hd S c
  set B := N / R
  have hB2 : B₀ + 2 ≤ B := (Nat.le_div_iff_mul_le hR).mpr (by rw [mul_comm]; exact hN)
  have hBpos : 0 < B := by omega
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity : 0 < R * (B₀ + 2)) hN
  set N₀ := R * B
  have hNle : N₀ ≤ N := Nat.mul_div_le N R
  have hNlt : N ≤ N₀ + R := (Nat.lt_mul_div_succ N hR).le
  have hRB : R ≤ N₀ := Nat.le_mul_of_pos_right R hBpos
  set W := Ioc N₀ (N₀ + B * J)
  have hsub : S ⊆ W := by
    refine Ioc_subset_Ioc hNle ?_
    dsimp only [J]
    calc N + 3 * K * N
        = (3 * K + 1) * N := by ring
      _ ≤ (3 * K + 1) * (N₀ + R) := Nat.mul_le_mul_left (3 * K + 1) hNlt
      _ = (3 * K + 1) * N₀ + (3 * K + 1) * R := by ring
      _ ≤ (3 * K + 1) * N₀ + (3 * K + 1) * N₀ :=
          Nat.add_le_add_left (Nat.mul_le_mul_left (3 * K + 1) hRB) _
      _ = N₀ + B * ((6 * K + 1) * R) := by dsimp only [N₀]; ring
  let c' : ℕ → ℝ := fun n => if n ∈ S then c n else 0
  have hform : combForm W c' = combForm S c :=
    (combForm_of_subset hsub fun n _ hn => if_neg hn).trans
      (combForm_congr fun n hn => if_pos hn)
  have hsq : ∑ n ∈ W, c' n ^ 2 = ∑ n ∈ S, c n ^ 2 := by
    rw [← sum_subset hsub fun n _ hn => by rw [if_neg hn]; ring]
    exact sum_congr rfl fun n hn => by rw [if_pos hn]
  have hdiv : N₀ / R = B := Nat.mul_div_cancel_left B hR
  -- Step 1: Block reduction with residual floor `κ₀`
  let σ := blockMean N₀ B J c'
  have h1 := hred N₀ J hRB (by rw [hdiv]; dsimp only [J, Q]; exact le_of_eq (by ring)) c'
  rw [hdiv, hform] at h1
  have hmass := sum_sq_eq_blockMean_add_residual hBpos N₀ J c'
  rw [hsq] at hmass
  -- Step 2: Continuum step-packet lower bound on block means `σ`
  have h2 := hB₀ B (by omega) σ
  have hpf_low : -M_step * ∑ j ∈ range J, σ j ^ 2 ≤ packetForm Q (stepPacket R J σ) := by
    have hab := (abs_le.mp (hM_step σ)).1
    linarith
  have hB0R : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have h2' : -(M_step + 1) * ((B : ℝ) * ∑ j ∈ range J, σ j ^ 2) ≤
      combForm W (fun n => σ (blockIndex N₀ B n)) := by
    have hm := mul_le_mul_of_nonneg_left hpf_low hB0R
    have hbsq := sum_blockFunction_sq (R := R) hBpos σ
    change _ ≤ combForm (Ioc (R * B) (R * B + B * J)) _
    rw [hbsq] at h2
    nlinarith
  -- Step 3: Bound every block mean `|σ j| ≤ (∑_{t ∈ T} |α t|) / B`
  have hσ_le : ∀ j ∈ range J, |σ j| ≤ (∑ t ∈ T, |α t|) / B := by
    intro j hj
    have hjJ := mem_range.mp hj
    have hbm : σ j = (∑ a ∈ range B, c' (N₀ + 1 + B * j + a)) / B := by
      dsimp only [σ]
      rw [blockMean, sum_filter_blockIndex hBpos N₀ J c' j, if_pos hjJ]
    rw [hbm, abs_div, abs_of_pos (by exact_mod_cast hBpos : (0 : ℝ) < B)]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have himg : ∑ a ∈ range B, c' (N₀ + 1 + B * j + a) =
        ∑ n ∈ Ioc (max (N₀ + B * j) N) (min (N₀ + B * j + B) (N + 3 * K * N)), c n := by
      have h1' : ∑ a ∈ range B, c' (N₀ + 1 + B * j + a) =
          ∑ n ∈ Ioc (N₀ + B * j) (N₀ + B * j + B), c' n := by
        rw [← image_range_block_eq_Ioc N₀ B j, sum_image]
        intro x _ y _ hxy; omega
      rw [h1']
      dsimp only [c']
      rw [← sum_filter]
      congr 1
      ext n
      dsimp only [S]
      simp only [mem_filter, mem_Ioc, max_lt_iff, le_min_iff]
      tauto
    rw [himg]
    set A₁ := max (N₀ + B * j) N
    set B₁ := min (N₀ + B * j + B) (N + 3 * K * N)
    have hswap : ∑ n ∈ Ioc A₁ B₁, c n =
        ∑ t ∈ T, α t * ∑ n ∈ Ioc A₁ B₁, centeredResidue (d t) (r t) n := by
      dsimp only [c]
      rw [sum_comm]
      exact sum_congr rfl fun t _ => (mul_sum _ _ _).symm
    rw [hswap]
    calc |∑ t ∈ T, α t * ∑ n ∈ Ioc A₁ B₁, centeredResidue (d t) (r t) n|
        ≤ ∑ t ∈ T, |α t * ∑ n ∈ Ioc A₁ B₁, centeredResidue (d t) (r t) n| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ T, |α t| * 1 := by
          refine sum_le_sum fun t ht => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            (abs_sum_centeredResidue_Ioc_le_one (hd t ht) (r t) A₁ B₁) (abs_nonneg _)
      _ = ∑ t ∈ T, |α t| := by simp
  have hsum_σ_sq : (B : ℝ) * ∑ j ∈ range J, σ j ^ 2 ≤
      ((J : ℝ) / (B : ℝ)) * (∑ t ∈ T, |α t|) ^ 2 := by
    have hBne : (B : ℝ) ≠ 0 := by exact_mod_cast hBpos.ne'
    have hpt : ∀ j ∈ range J, σ j ^ 2 ≤ ((∑ t ∈ T, |α t|) / B) ^ 2 := fun j hj => by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hσ_le j hj) 2
    calc (B : ℝ) * ∑ j ∈ range J, σ j ^ 2
        ≤ (B : ℝ) * ∑ _j ∈ range J, ((∑ t ∈ T, |α t|) / B) ^ 2 :=
          mul_le_mul_of_nonneg_left (sum_le_sum hpt) hB0R
      _ = (B : ℝ) * ((J : ℝ) * (((∑ t ∈ T, |α t|) / B) ^ 2)) := by
          rw [sum_const, card_range, nsmul_eq_mul]
      _ = ((J : ℝ) / (B : ℝ)) * (∑ t ∈ T, |α t|) ^ 2 := by
          field_simp [hBne]
  have hJB_le : (J : ℝ) / (B : ℝ) ≤ 2 * (R : ℝ) * (J : ℝ) / (N : ℝ) := by
    have hN2RB : (N : ℝ) ≤ 2 * (R : ℝ) * (B : ℝ) := by
      have hnat : N ≤ 2 * R * B :=
        calc N ≤ N₀ + R := hNlt
          _ ≤ N₀ + N₀ := Nat.add_le_add_left hRB _
          _ = 2 * R * B := by dsimp only [N₀]; ring
      exact_mod_cast hnat
    rw [div_le_div_iff₀ (by exact_mod_cast hBpos) (by exact_mod_cast hNpos)]
    calc (J : ℝ) * (N : ℝ)
        ≤ (J : ℝ) * (2 * (R : ℝ) * (B : ℝ)) :=
          mul_le_mul_of_nonneg_left hN2RB (Nat.cast_nonneg J)
      _ = 2 * (R : ℝ) * (J : ℝ) * (B : ℝ) := by ring
  have hcomb_S : κ₀ * ∑ n ∈ S, c n ^ 2 - C / (N : ℝ) * (∑ t ∈ T, |α t|) ^ 2 ≤ combForm S c := by
    have hbsq : ∑ n ∈ W, σ (blockIndex N₀ B n) ^ 2 = (B : ℝ) * ∑ j ∈ range J, σ j ^ 2 :=
      sum_blockFunction_sq (R := R) hBpos σ
    have hcomb1 : κ₀ * ∑ n ∈ S, c n ^ 2 -
        (M_step + κ₀ + 2) * ((B : ℝ) * ∑ j ∈ range J, σ j ^ 2) ≤ combForm S c := by
      -- Combine `h1`, `hmass`, and `h2'`
      have hres_eq : ∑ n ∈ W, (c' n - σ (blockIndex N₀ B n)) ^ 2 =
          ∑ n ∈ S, c n ^ 2 - (B : ℝ) * ∑ j ∈ range J, σ j ^ 2 := by
        dsimp only [σ] at hbsq ⊢
        linarith [hmass, hbsq]
      have hmul_res : κ₀ * ∑ n ∈ W, (c' n - σ (blockIndex N₀ B n)) ^ 2 =
          κ₀ * ∑ n ∈ S, c n ^ 2 - κ₀ * ((B : ℝ) * ∑ j ∈ range J, σ j ^ 2) := by
        rw [hres_eq]; ring
      dsimp only [σ] at h2' hbsq ⊢
      linarith [h1, h2', hbsq, hmul_res]
    have herr_le : (M_step + κ₀ + 2) * ((B : ℝ) * ∑ j ∈ range J, σ j ^ 2) ≤
        C / (N : ℝ) * (∑ t ∈ T, |α t|) ^ 2 := by
      have hpos1 : 0 ≤ M_step + κ₀ + 2 := by positivity
      calc (M_step + κ₀ + 2) * ((B : ℝ) * ∑ j ∈ range J, σ j ^ 2)
          ≤ (M_step + κ₀ + 2) * (((J : ℝ) / (B : ℝ)) * (∑ t ∈ T, |α t|) ^ 2) :=
            mul_le_mul_of_nonneg_left hsum_σ_sq hpos1
        _ ≤ (M_step + κ₀ + 2) * ((2 * (R : ℝ) * (J : ℝ) / (N : ℝ)) * (∑ t ∈ T, |α t|) ^ 2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hJB_le (sq_nonneg _)) hpos1
        _ = (2 * (R : ℝ) * (J : ℝ) * (M_step + κ₀ + 2)) / (N : ℝ) * (∑ t ∈ T, |α t|) ^ 2 := by
            ring
        _ ≤ C / (N : ℝ) * (∑ t ∈ T, |α t|) ^ 2 := by
            refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ (by positivity))
              (sq_nonneg _)
            dsimp only [C]
            nlinarith [show (0 : ℝ) ≤ (R : ℝ) * J by positivity]
    linarith
  -- Step 4: Transfer from `combForm` (`Λ`) to `combFormW w` via bounded-ratio Schur bound
  have hschur := abs_contactTerm_lateComb_self_le (fun k => w k - Λ k) N K c
  have hw_eq := combFormW_eq w S c
  change combFormW w S c = combForm S c - contactTerm (fun k => w k - Λ k) S c c at hw_eq
  have hcont_up : contactTerm (fun k => w k - Λ k) S c c ≤ D_w * ∑ n ∈ S, c n ^ 2 :=
    (le_abs_self _).trans hschur
  have hκ_split : κ₀ * ∑ n ∈ S, c n ^ 2 = κ * ∑ n ∈ S, c n ^ 2 + D_w * ∑ n ∈ S, c n ^ 2 := by
    dsimp only [κ₀]; ring
  linarith

/-- Whenever a linear combination of centered congruence indicators satisfies the
sub-macroscopic cost bound `(∑ |α_t|)^2 ≤ δ N ∑_{n ∈ S} c(n)^2` with `δ = 1 / C_{K, w, 1}`,
its diagonal and real-place budget pays its `w`-weighted mixed prime debit on `S`. -/
theorem eventually_mixedPrimeDebitW_le_diagRealBudget_of_cost (K : ℕ)
    (w : ℕ → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ {ι : Type*} (T : Finset ι) (d r : ι → ℕ) (α : ι → ℝ),
        (∀ t ∈ T, 0 < d t) →
        let S := Ioc N (N + 3 * K * N)
        let c := fun n => ∑ t ∈ T, α t * centeredResidue (d t) (r t) n
        (∑ t ∈ T, |α t|) ^ 2 ≤ δ * (N : ℝ) * ∑ n ∈ S, c n ^ 2 →
        mixedPrimeDebitW w S c ≤ diagRealBudget S c := by
  obtain ⟨C, hC, hev⟩ := eventually_combFormW_controlled_residue_ge K w zero_lt_one
  refine ⟨1 / C, by positivity, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1 ι T d r α hd hcost
  set S := Ioc N (N + 3 * K * N)
  set c := fun n => ∑ t ∈ T, α t * centeredResidue (d t) (r t) n
  rw [mixedPrimeDebitW_le_diagRealBudget_iff]
  have hmain := hN T d r α hd
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcost' : C / (N : ℝ) * (∑ t ∈ T, |α t|) ^ 2 ≤ 1 * ∑ n ∈ S, c n ^ 2 := by
    calc C / (N : ℝ) * (∑ t ∈ T, |α t|) ^ 2
        ≤ C / (N : ℝ) * ((1 / C) * (N : ℝ) * ∑ n ∈ S, c n ^ 2) :=
          mul_le_mul_of_nonneg_left hcost (by positivity)
      _ = 1 * ∑ n ∈ S, c n ^ 2 := by field_simp [hC.ne', hN0.ne']
  linarith

/-! ### Complete solution of the two-prime pilot (ordinary and Liouville-twisted) -/

private theorem log_le_four_fourthRoot {N : ℕ} (hN : 1 ≤ N) :
    Real.log N ≤ 4 * Real.sqrt (Real.sqrt N) := by
  set u := Real.sqrt (Real.sqrt N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hu0 : 0 < u := by dsimp only [u]; positivity
  have hu4 : u ^ 4 = (N : ℝ) := by
    dsimp only [u]
    have h1 : Real.sqrt (Real.sqrt N) ^ 2 = Real.sqrt N := Real.sq_sqrt (Real.sqrt_nonneg _)
    calc Real.sqrt (Real.sqrt N) ^ 4
        = (Real.sqrt (Real.sqrt N) ^ 2) ^ 2 := by ring
      _ = Real.sqrt N ^ 2 := by rw [h1]
      _ = N := Real.sq_sqrt hN0.le
  rw [← hu4, Real.log_pow]
  have hlog := Real.log_le_sub_one_of_pos hu0
  push_cast
  linarith

private theorem sum_centeredMultiple_sq_lateComb_ge_of_le_sqrt
    {K N d : ℕ} {c₂ : ℝ} (hc₂ : 0 < c₂)
    (hN : c₂ * Real.sqrt N ≤ (K : ℝ) * N)
    (hd2 : 2 ≤ d) (hdd : (d : ℝ) ≤ c₂ * Real.sqrt N) :
    ((K : ℝ) / c₂) * Real.sqrt N ≤
      ∑ n ∈ Ioc N (N + 3 * K * N), centeredMultiple d n ^ 2 := by
  have hd0 : 0 < d := by omega
  have hdR0 : (0 : ℝ) < d := by exact_mod_cast hd0
  have hstep := sum_centeredMultiple_sq_Ioc_ge hd0 N (N + 3 * K * N)
  rw [Nat.add_sub_cancel_left] at hstep
  have hdKN : d ≤ K * N := by
    have : (d : ℝ) ≤ ((K * N : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hdiv_ge : (2 * (K : ℝ) * N) / (d : ℝ) ≤ (((3 * K * N) / d : ℕ) : ℝ) := by
    rw [div_le_iff₀ hdR0]
    have hlt : 3 * K * N < d * ((3 * K * N) / d + 1) := Nat.lt_mul_div_succ _ hd0
    have hltR : (3 : ℝ) * K * N ≤ (d : ℝ) * (((3 * K * N) / d : ℕ) : ℝ) + d := by
      have : ((3 * K * N : ℕ) : ℝ) ≤ ((d * ((3 * K * N) / d + 1) : ℕ) : ℝ) :=
        by exact_mod_cast hlt.le
      push_cast at this
      linarith
    have hdKNR : (d : ℝ) ≤ (K : ℝ) * N := by exact_mod_cast hdKN
    linarith
  have hfac : (1 / 2 : ℝ) ≤ 1 - 1 / (d : ℝ) := by
    have : (1 : ℝ) / d ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hd2)
    linarith
  have hKN_div : ((K : ℝ) / c₂) * Real.sqrt N ≤ (K : ℝ) * N / (d : ℝ) := by
    rw [le_div_iff₀ hdR0]
    have hsqN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
    calc ((K : ℝ) / c₂) * Real.sqrt N * d
        ≤ ((K : ℝ) / c₂) * Real.sqrt N * (c₂ * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left hdd (by positivity)
      _ = (K : ℝ) * (Real.sqrt N * Real.sqrt N) := by field_simp [hc₂.ne']; ring
      _ = (K : ℝ) * N := by rw [hsqN]
  calc ((K : ℝ) / c₂) * Real.sqrt N
      ≤ (K : ℝ) * N / (d : ℝ) := hKN_div
    _ = ((2 * (K : ℝ) * N) / (d : ℝ)) * (1 / 2) := by ring
    _ ≤ (((3 * K * N) / d : ℕ) : ℝ) * (1 - 1 / (d : ℝ)) :=
        mul_le_mul hdiv_ge hfac (by norm_num) (by positivity)
    _ ≤ ∑ n ∈ Ioc N (N + 3 * K * N), centeredMultiple d n ^ 2 := hstep

/-- **Two-prime pilot positivity and Cauchy–Schwarz.** For every comb width `K ≥ 1`,
horizon scale `c_2 > 0`, and contact weight `w`, eventually in `N`, for all distinct
primes `p ≠ q` up to `⌊c_2 √N⌋`:
`A = combFormW w S v_p > 0`, `C = combFormW w S v_q > 0`, `B^2 ≤ A C`, and `combFormW w S`
is nonnegative on the entire two-dimensional plane `span{v_p, v_q}`. -/
theorem eventually_pilot_pos_and_cauchy_schwarz {K : ℕ} (hK : 1 ≤ K)
    {c₂ : ℝ} (hc₂ : 0 < c₂) (w : ℕ → ℝ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ {p q : ℕ}, p.Prime → q.Prime → p ≠ q →
        p ≤ ⌊c₂ * Real.sqrt N⌋₊ → q ≤ ⌊c₂ * Real.sqrt N⌋₊ →
        let S := Ioc N (N + 3 * K * N)
        let vp := centeredMultiple p
        let vq := centeredMultiple q
        (K : ℝ) / c₂ * Real.sqrt N ≤ combFormW w S vp ∧
        (K : ℝ) / c₂ * Real.sqrt N ≤ combFormW w S vq ∧
        0 < combFormW w S vp ∧
        0 < combFormW w S vq ∧
        formBilinW w S vp vq ^ 2 ≤ combFormW w S vp * combFormW w S vq ∧
        ∀ α β : ℝ, 0 ≤ combFormW w S (fun n => α * vp n + β * vq n) := by
  obtain ⟨C₁, hC₁, hev₁⟩ := eventually_combFormW_controlled_residue_ge K w (κ := 2) (by norm_num)
  set C_B : ℝ := 16 + 4 * (K : ℝ) + 4 * Real.log (1 + 3 * (K : ℝ)) +
    4 * ∑ r ∈ Icc 2 (3 * K), |w r|
  have hCB_pos : 0 < C_B := by
    dsimp only [C_B]
    have : 0 ≤ Real.log (1 + 3 * (K : ℝ)) :=
      Real.log_nonneg (by linarith [show (0 : ℝ) ≤ K from Nat.cast_nonneg K])
    have : 0 ≤ ∑ r ∈ Icc 2 (3 * K), |w r| := sum_nonneg fun _ _ => abs_nonneg _
    positivity
  set γ : ℝ := (K : ℝ) / c₂
  have hγ : 0 < γ := by dsimp only [γ]; positivity
  set N_min : ℕ := ⌈c₂ ^ 2⌉₊ + ⌈C₁ / γ⌉₊ + ⌈(5 * C_B / γ) ^ 4⌉₊ + 4
  filter_upwards [hev₁, eventually_ge_atTop N_min] with N hN₁ hN p q hp hq hpq hp_le hq_le
  set S := Ioc N (N + 3 * K * N)
  set vp := centeredMultiple p
  set vq := centeredMultiple q
  have hN1 : 1 ≤ N := by dsimp only [N_min] at hN; omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsqrt_pos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hN_ge_c2 : c₂ ^ 2 ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈c₂ ^ 2⌉₊ ≤ N by dsimp only [N_min] at hN; omega))
  have hc2_sqrt_le : c₂ * Real.sqrt N ≤ (K : ℝ) * N := by
    have h1 : c₂ ≤ Real.sqrt N := by
      rw [← Real.sqrt_sq hc₂.le]
      exact Real.sqrt_le_sqrt hN_ge_c2
    have h2 : c₂ * Real.sqrt N ≤ Real.sqrt N * Real.sqrt N :=
      mul_le_mul_of_nonneg_right h1 hsqrt_pos.le
    rw [Real.mul_self_sqrt hN0.le] at h2
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    exact h2.trans (le_mul_of_one_le_left hN0.le hK1)
  have hself (d : ℕ) (hd : d.Prime) (hd_le : d ≤ ⌊c₂ * Real.sqrt N⌋₊) :
      γ * Real.sqrt N ≤ combFormW w S (centeredMultiple d) := by
    have hdR : (d : ℝ) ≤ c₂ * Real.sqrt N :=
      (Nat.cast_le.mpr hd_le).trans (Nat.floor_le (by positivity))
    have hmass := sum_centeredMultiple_sq_lateComb_ge_of_le_sqrt hc₂ hc2_sqrt_le hd.two_le hdR
    have hsing := hN₁ ({0} : Finset ℕ) (fun _ => d) (fun _ => 0) (fun _ => 1)
      (fun _ _ => hd.pos)
    have hce : (fun n => ∑ _t ∈ ({0} : Finset ℕ), (1 : ℝ) * centeredResidue d 0 n) =
        centeredMultiple d := by
      funext n
      rw [sum_singleton, one_mul, ← centeredMultiple_eq_centeredResidue hd.pos]
    rw [hce, sum_singleton, abs_one, one_pow, mul_one] at hsing
    have hC1_le : C₁ / (N : ℝ) ≤ γ * Real.sqrt N := by
      have hN_C1 : C₁ / γ ≤ (N : ℝ) :=
        (Nat.le_ceil _).trans
          (by exact_mod_cast (show ⌈C₁ / γ⌉₊ ≤ N by dsimp only [N_min] at hN; omega))
      have h1 : C₁ / (N : ℝ) ≤ γ := by
        rw [div_le_iff₀ hN0]
        have := (div_le_iff₀ hγ).mp hN_C1
        linarith
      have hsqrt1 : (1 : ℝ) ≤ Real.sqrt N := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hN1)
      calc C₁ / (N : ℝ) ≤ γ * 1 := by linarith
        _ ≤ γ * Real.sqrt N := mul_le_mul_of_nonneg_left hsqrt1 hγ.le
    dsimp only [γ] at hmass ⊢
    linarith
  have hA := hself p hp hp_le
  have hC := hself q hq hq_le
  have hA_pos : 0 < combFormW w S vp := lt_of_lt_of_le (mul_pos hγ hsqrt_pos) hA
  have hC_pos : 0 < combFormW w S vq := lt_of_lt_of_le (mul_pos hγ hsqrt_pos) hC
  -- Bound `B^2 ≤ A * C`
  have hB_abs := abs_formBilinW_distinct_primes_le w N K hp hq hpq
  set u := Real.sqrt (Real.sqrt N)
  have hu1 : (1 : ℝ) ≤ u := by
    dsimp only [u]
    have h1 : (1 : ℝ) ≤ Real.sqrt N := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hN1)
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt h1
  have hlog_u : 1 + Real.log N ≤ 5 * u := by
    have := log_le_four_fourthRoot hN1
    linarith
  have hB_le : |formBilinW w S vp vq| ≤ 5 * C_B * u := by
    calc |formBilinW w S vp vq|
        ≤ C_B * (1 + Real.log N) := hB_abs
      _ ≤ C_B * (5 * u) := mul_le_mul_of_nonneg_left hlog_u hCB_pos.le
      _ = 5 * C_B * u := by ring
  have h5CB_le : 5 * C_B * u ≤ γ * Real.sqrt N := by
    have hu2 : u * u = Real.sqrt N := Real.mul_self_sqrt hsqrt_pos.le
    have hN_CB : (5 * C_B / γ) ^ 4 ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans
        (by exact_mod_cast (show ⌈(5 * C_B / γ) ^ 4⌉₊ ≤ N by dsimp only [N_min] at hN; omega))
    have hsqrt_CB2 : (5 * C_B / γ) ^ 2 ≤ Real.sqrt N := by
      have hsq4 : ((5 * C_B / γ) ^ 2) ^ 2 = (5 * C_B / γ) ^ 4 := by ring
      rw [← Real.sqrt_sq (by positivity : 0 ≤ (5 * C_B / γ) ^ 2), hsq4]
      exact Real.sqrt_le_sqrt hN_CB
    have hu_CB : 5 * C_B / γ ≤ u := by
      dsimp only [u]
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 5 * C_B / γ)]
      exact Real.sqrt_le_sqrt hsqrt_CB2
    have hmul_u := mul_le_mul_of_nonneg_right ((le_div_iff₀ hγ).mp hu_CB) (show 0 ≤ u by linarith)
    calc 5 * C_B * u ≤ (γ * u) * u := hmul_u
      _ = γ * (u * u) := by ring
      _ = γ * Real.sqrt N := by rw [hu2]
  have hBA : |formBilinW w S vp vq| ≤ combFormW w S vp :=
    (hB_le.trans h5CB_le).trans hA
  have hBC : |formBilinW w S vp vq| ≤ combFormW w S vq :=
    (hB_le.trans h5CB_le).trans hC
  have hCS : formBilinW w S vp vq ^ 2 ≤ combFormW w S vp * combFormW w S vq := by
    rw [← sq_abs, sq]
    exact mul_le_mul hBA hBC (abs_nonneg _) hA_pos.le
  exact ⟨hA, hC, hA_pos, hC_pos, hCS,
    combFormW_two_span_nonneg_of_cauchy_schwarz hA_pos.le hC_pos.le hCS⟩

/-- Specialization of the two-prime pilot to the untwisted Weil form (`w = Λ`). -/
theorem eventually_pilot_vonMangoldt_pos_and_cauchy_schwarz {K : ℕ} (hK : 1 ≤ K)
    {c₂ : ℝ} (hc₂ : 0 < c₂) :
    ∀ᶠ N : ℕ in atTop,
      ∀ {p q : ℕ}, p.Prime → q.Prime → p ≠ q →
        p ≤ ⌊c₂ * Real.sqrt N⌋₊ → q ≤ ⌊c₂ * Real.sqrt N⌋₊ →
        let S := Ioc N (N + 3 * K * N)
        let vp := centeredMultiple p
        let vq := centeredMultiple q
        0 < combForm S vp ∧
        0 < combForm S vq ∧
        formBilin S vp vq ^ 2 ≤ combForm S vp * combForm S vq ∧
        ∀ α β : ℝ, 0 ≤ combForm S (fun n => α * vp n + β * vq n) := by
  filter_upwards [eventually_pilot_pos_and_cauchy_schwarz hK hc₂ (fun k => (Λ k : ℝ))]
    with N hN p q hp hq hpq hp_le hq_le
  obtain ⟨_, _, hA, hC, hCS, hspan⟩ := hN hp hq hpq hp_le hq_le
  simpa only [combFormW_vonMangoldt, formBilinW_vonMangoldt] using ⟨hA, hC, hCS, hspan⟩

/-- Specialization of the two-prime pilot to `SelectiveArithmetic.liouvilleWeight`. -/
theorem eventually_pilot_liouville_pos_and_cauchy_schwarz {K : ℕ} (hK : 1 ≤ K)
    {c₂ : ℝ} (hc₂ : 0 < c₂) :
    ∀ᶠ N : ℕ in atTop,
      ∀ {p q : ℕ}, p.Prime → q.Prime → p ≠ q →
        p ≤ ⌊c₂ * Real.sqrt N⌋₊ → q ≤ ⌊c₂ * Real.sqrt N⌋₊ →
        let S := Ioc N (N + 3 * K * N)
        let vp := centeredMultiple p
        let vq := centeredMultiple q
        0 < combFormW SelectiveArithmetic.liouvilleWeight S vp ∧
        0 < combFormW SelectiveArithmetic.liouvilleWeight S vq ∧
        formBilinW SelectiveArithmetic.liouvilleWeight S vp vq ^ 2 ≤
          combFormW SelectiveArithmetic.liouvilleWeight S vp *
            combFormW SelectiveArithmetic.liouvilleWeight S vq ∧
        ∀ α β : ℝ,
          0 ≤ combFormW SelectiveArithmetic.liouvilleWeight S (fun n => α * vp n + β * vq n) := by
  filter_upwards [eventually_pilot_pos_and_cauchy_schwarz hK hc₂
      SelectiveArithmetic.liouvilleWeight]
    with N hN p q hp hq hpq hp_le hq_le
  obtain ⟨_, _, hA, hC, hCS, hspan⟩ := hN hp hq hpq hp_le hq_le
  exact ⟨hA, hC, hCS, hspan⟩

/-! ### Unrestricted `√N`-horizon prime span positivity -/

private theorem sq_sum_le_card_mul_sum_sq {ι : Type*} (T : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ T, f i) ^ 2 ≤ (T.card : ℝ) * ∑ i ∈ T, f i ^ 2 := by
  have hexp : (∑ i ∈ T, f i) ^ 2 = ∑ i ∈ T, ∑ j ∈ T, f i * f j := by
    rw [sq, sum_mul]
    exact sum_congr rfl fun i _ => mul_sum _ _ _
  have h2 : 2 * (∑ i ∈ T, f i) ^ 2 ≤ 2 * ((T.card : ℝ) * ∑ i ∈ T, f i ^ 2) := by
    rw [hexp, mul_sum]
    calc ∑ i ∈ T, 2 * ∑ j ∈ T, f i * f j
        = ∑ i ∈ T, ∑ j ∈ T, 2 * (f i * f j) := sum_congr rfl fun _ _ => mul_sum _ _ _
      _ ≤ ∑ i ∈ T, ∑ j ∈ T, (f i ^ 2 + f j ^ 2) :=
          sum_le_sum fun i _ => sum_le_sum fun j _ => by nlinarith [sq_nonneg (f i - f j)]
      _ = 2 * ((T.card : ℝ) * ∑ i ∈ T, f i ^ 2) := by
          simp only [sum_add_distrib, sum_const, nsmul_eq_mul]
          rw [← mul_sum]
          ring
  linarith

/-- Elementary Chebyshev prime-counting bound `#(Nat.primesLE X) ≤ √X + (2 log 4) X / log X`
for `X ≥ 4`. -/
theorem card_primesLE_le {X : ℕ} (hX : 4 ≤ X) :
    ((Nat.primesLE X).card : ℝ) ≤
      Real.sqrt X + (2 * Real.log 4) * (X : ℝ) / Real.log X := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hlogX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  set s := ⌊Real.sqrt X⌋₊
  have hpart : (Nat.primesLE X).card =
      ((Nat.primesLE X).filter (· ≤ s)).card +
        ((Nat.primesLE X).filter (fun p => ¬ p ≤ s)).card :=
    (card_filter_add_card_filter_not (s := Nat.primesLE X) (p := (· ≤ s))).symm
  have hlow : (((Nat.primesLE X).filter (· ≤ s)).card : ℝ) ≤ Real.sqrt X := by
    have hsub : (Nat.primesLE X).filter (· ≤ s) ⊆ Icc 1 s := fun p hp => by
      obtain ⟨hpP, hps⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hpP).pos, hps⟩
    calc (((Nat.primesLE X).filter (· ≤ s)).card : ℝ)
        ≤ ((Icc 1 s).card : ℝ) := by exact_mod_cast card_le_card hsub
      _ = (s : ℝ) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
      _ ≤ Real.sqrt X := Nat.floor_le (Real.sqrt_nonneg X)
  have hhigh : (((Nat.primesLE X).filter (fun p => ¬ p ≤ s)).card : ℝ) ≤
      (2 * Real.log 4) * (X : ℝ) / Real.log X := by
    set H := (Nat.primesLE X).filter (fun p => ¬ p ≤ s)
    have hlog_each : ∀ p ∈ H, (1 / 2 : ℝ) * Real.log X ≤ Real.log p := fun p hp => by
      obtain ⟨_, hps⟩ := mem_filter.mp hp
      have hgt : Real.sqrt X < p := Nat.lt_of_floor_lt (not_le.mp hps)
      have hsq : (X : ℝ) ≤ (p : ℝ) ^ 2 := by
        rw [← Real.sq_sqrt hX0.le]
        exact pow_le_pow_left₀ (Real.sqrt_nonneg X) hgt.le 2
      have hlog2 := Real.log_le_log hX0 hsq
      rw [Real.log_pow, Nat.cast_ofNat] at hlog2
      linarith
    have hsum_H : (H.card : ℝ) * ((1 / 2 : ℝ) * Real.log X) ≤ (X : ℝ) * Real.log 4 := by
      calc (H.card : ℝ) * ((1 / 2 : ℝ) * Real.log X)
          = ∑ _p ∈ H, (1 / 2 : ℝ) * Real.log X := by rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ p ∈ H, Real.log p := sum_le_sum hlog_each
        _ ≤ ∑ p ∈ Nat.primesLE X, Real.log p :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ =>
              Real.log_natCast_nonneg p
        _ ≤ (X : ℝ) * Real.log 4 := _root_.RHTower.Sieve.sum_log_primesLE_le X
    rw [le_div_iff₀ hlogX]
    linarith
  rw [hpart, Nat.cast_add]
  linarith

/-- **Unrestricted `√N`-horizon prime span positivity.** For every comb width `K ≥ 1`,
horizon scale `C_0 > 0`, margin `κ > 0`, and contact weight `w`, eventually in `N`,
every unrestricted real linear combination `c(n) = ∑_{p ≤ ⌊C_0 √N⌋} α_p v_p(n)` satisfies
`κ ∑_{n ∈ S} c(n)^2 ≤ combFormW w S c`. -/
theorem eventually_combFormW_primeSpan_sqrt_ge {K : ℕ} (hK : 1 ≤ K)
    {C₀ : ℝ} (hC₀ : 0 < C₀) (w : ℕ → ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ N : ℕ in atTop, ∀ α : ℕ → ℝ,
      let S := Ioc N (N + 3 * K * N)
      let P := Nat.primesLE ⌊C₀ * Real.sqrt N⌋₊
      let c := fun n => ∑ p ∈ P, α p * centeredMultiple p n
      κ * ∑ n ∈ S, c n ^ 2 ≤ combFormW w S c := by
  obtain ⟨C₁, hC₁, hev₁⟩ := eventually_combFormW_controlled_residue_ge K w
    (show 0 < 2 * κ by positivity)
  set γ : ℝ := (K : ℝ) / C₀
  have hγ : 0 < γ := by dsimp only [γ]; positivity
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set L₂ : ℝ := 16 * Real.log 4 * C₀ / γ + 1
  have hL₂ : 0 < L₂ := by dsimp only [L₂]; positivity
  set N_min : ℕ :=
    ⌈C₀ ^ 2⌉₊ + ⌈((Real.exp L₂ + 5) / C₀) ^ 2⌉₊ +
      ⌈(8 * Real.sqrt C₀ / γ) ^ 4⌉₊ + ⌈2 * C₁ * C₀ / (γ * κ)⌉₊ + 4
  filter_upwards [hev₁, eventually_ge_atTop N_min] with N hN₁ hN α
  set S := Ioc N (N + 3 * K * N)
  set X := ⌊C₀ * Real.sqrt N⌋₊
  set P := Nat.primesLE X
  set c := fun n => ∑ p ∈ P, α p * centeredMultiple p n
  have hN1 : 1 ≤ N := by dsimp only [N_min] at hN; omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsqrt_pos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  -- 1. Establish `4 ≤ X`, `Real.exp L₂ ≤ X`, and `C₀ * √N ≤ K * N`
  have hexp_le_C0 : Real.exp L₂ + 5 ≤ C₀ * Real.sqrt N := by
    have hN_exp : ((Real.exp L₂ + 5) / C₀) ^ 2 ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans
        (by exact_mod_cast (show ⌈((Real.exp L₂ + 5) / C₀) ^ 2⌉₊ ≤ N by dsimp only [N_min] at hN; omega))
    have h1 : (Real.exp L₂ + 5) / C₀ ≤ Real.sqrt N := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ (Real.exp L₂ + 5) / C₀)]
      exact Real.sqrt_le_sqrt hN_exp
    exact (div_le_iff₀ hC₀).mp h1
  have hX_gt : C₀ * Real.sqrt N - 1 < (X : ℝ) := Nat.sub_one_lt_floor _
  have hexp_le_X : Real.exp L₂ ≤ (X : ℝ) := by linarith
  have hX4 : 4 ≤ X := by
    have : (4 : ℝ) ≤ (X : ℝ) := by linarith [Real.exp_pos L₂]
    exact_mod_cast this
  have hC0_sqrt_le : C₀ * Real.sqrt N ≤ (K : ℝ) * N := by
    have hN_C0 : C₀ ^ 2 ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans
        (by exact_mod_cast (show ⌈C₀ ^ 2⌉₊ ≤ N by dsimp only [N_min] at hN; omega))
    have h1 : C₀ ≤ Real.sqrt N := by
      rw [← Real.sqrt_sq hC₀.le]; exact Real.sqrt_le_sqrt hN_C0
    have h2 : C₀ * Real.sqrt N ≤ Real.sqrt N * Real.sqrt N :=
      mul_le_mul_of_nonneg_right h1 hsqrt_pos.le
    rw [Real.mul_self_sqrt hN0.le] at h2
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    exact h2.trans (le_mul_of_one_le_left hN0.le hK1)
  -- 2. Bound `2 * #P ≤ (γ / 2) * √N`
  have hcard_le : 2 * (P.card : ℝ) ≤ (γ / 2) * Real.sqrt N := by
    have hcp := card_primesLE_le hX4
    have hX_le : (X : ℝ) ≤ C₀ * Real.sqrt N := Nat.floor_le (by positivity)
    -- Bound `2 * √X ≤ (γ / 4) * √N`
    set u := Real.sqrt (Real.sqrt N)
    have hu2 : u * u = Real.sqrt N := Real.mul_self_sqrt hsqrt_pos.le
    have h2sqrtX : 2 * Real.sqrt X ≤ (γ / 4) * Real.sqrt N := by
      have hsqrtX : Real.sqrt X ≤ Real.sqrt C₀ * u := by
        rw [← Real.sqrt_mul hC₀.le]
        exact Real.sqrt_le_sqrt hX_le
      have hN_u : (8 * Real.sqrt C₀ / γ) ^ 4 ≤ (N : ℝ) :=
        (Nat.le_ceil _).trans
          (by exact_mod_cast (show ⌈(8 * Real.sqrt C₀ / γ) ^ 4⌉₊ ≤ N by dsimp only [N_min] at hN; omega))
      have hsqrt_u2 : (8 * Real.sqrt C₀ / γ) ^ 2 ≤ Real.sqrt N := by
        have hsq4 : ((8 * Real.sqrt C₀ / γ) ^ 2) ^ 2 = (8 * Real.sqrt C₀ / γ) ^ 4 := by ring
        rw [← Real.sqrt_sq (by positivity : 0 ≤ (8 * Real.sqrt C₀ / γ) ^ 2), hsq4]
        exact Real.sqrt_le_sqrt hN_u
      have hu_ge : 8 * Real.sqrt C₀ / γ ≤ u := by
        dsimp only [u]
        rw [← Real.sqrt_sq (by positivity : 0 ≤ 8 * Real.sqrt C₀ / γ)]
        exact Real.sqrt_le_sqrt hsqrt_u2
      have hmul_u := mul_le_mul_of_nonneg_right ((le_div_iff₀ hγ).mp hu_ge)
        (show 0 ≤ u by dsimp only [u]; positivity)
      calc 2 * Real.sqrt X
          ≤ 2 * (Real.sqrt C₀ * u) := mul_le_mul_of_nonneg_left hsqrtX (by norm_num)
        _ = (1 / 4) * (8 * Real.sqrt C₀ * u) := by ring
        _ ≤ (1 / 4) * ((γ * u) * u) := mul_le_mul_of_nonneg_left hmul_u (by norm_num)
        _ = (γ / 4) * (u * u) := by ring
        _ = (γ / 4) * Real.sqrt N := by rw [hu2]
    -- Bound `2 * ((2 log 4) X / log X) ≤ (γ / 4) * √N`
    have hlogX_ge : L₂ ≤ Real.log X :=
      (Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < X))).mpr hexp_le_X
    have hlogX_pos : 0 < Real.log X := lt_of_lt_of_le hL₂ hlogX_ge
    have hhigh_term : 2 * ((2 * Real.log 4) * (X : ℝ) / Real.log X) ≤ (γ / 4) * Real.sqrt N := by
      have h1 : (2 * Real.log 4) * (X : ℝ) / Real.log X ≤
          (2 * Real.log 4) * (C₀ * Real.sqrt N) / L₂ := by
        calc (2 * Real.log 4) * (X : ℝ) / Real.log X
            ≤ (2 * Real.log 4) * (C₀ * Real.sqrt N) / Real.log X :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hX_le (by positivity)) hlogX_pos.le
          _ ≤ (2 * Real.log 4) * (C₀ * Real.sqrt N) / L₂ :=
              div_le_div_of_nonneg_left (by positivity) hL₂ hlogX_ge
      have h2 : 2 * ((2 * Real.log 4) * (C₀ * Real.sqrt N) / L₂) ≤ (γ / 4) * Real.sqrt N := by
        rw [show 2 * ((2 * Real.log 4) * (C₀ * Real.sqrt N) / L₂) =
          (4 * Real.log 4 * C₀ / L₂) * Real.sqrt N by ring]
        refine mul_le_mul_of_nonneg_right ?_ hsqrt_pos.le
        rw [div_le_iff₀ hL₂]
        dsimp only [L₂]
        have hcancel : γ / 4 * (16 * Real.log 4 * C₀ / γ + 1) =
            4 * Real.log 4 * C₀ + γ / 4 := by field_simp [hγ.ne']; ring
        linarith
      linarith
    linarith
  -- 3. Gram lower bound `(γ / 2) * √N * ∑_{p ∈ P} α_p^2 ≤ ∑_{n ∈ S} c(n)^2`
  have hgram : (γ / 2) * Real.sqrt N * ∑ p ∈ P, α p ^ 2 ≤ ∑ n ∈ S, c n ^ 2 := by
    have hexp_c : ∑ n ∈ S, c n ^ 2 =
        (∑ p ∈ P, α p ^ 2 * ∑ n ∈ S, centeredMultiple p n ^ 2) +
          ∑ p ∈ P, ∑ q ∈ P.erase p,
            α p * α q * ∑ n ∈ S, centeredMultiple p n * centeredMultiple q n := by
      have h1 : ∀ n ∈ S, c n ^ 2 =
          (∑ p ∈ P, α p ^ 2 * centeredMultiple p n ^ 2) +
            ∑ p ∈ P, ∑ q ∈ P.erase p,
              α p * α q * (centeredMultiple p n * centeredMultiple q n) := fun n _ => by
        dsimp only [c]
        rw [sq, sum_mul]
        have hrow : ∀ p ∈ P, (α p * centeredMultiple p n) * (∑ q ∈ P, α q * centeredMultiple q n) =
            α p ^ 2 * centeredMultiple p n ^ 2 +
              ∑ q ∈ P.erase p, α p * α q * (centeredMultiple p n * centeredMultiple q n) := by
          intro p hp
          rw [mul_sum, ← add_sum_erase _ _ hp]
          congr 1
          · ring
          · exact sum_congr rfl fun _ _ => by ring
        rw [sum_congr rfl hrow, sum_add_distrib]
      rw [sum_congr rfl h1, sum_add_distrib]
      congr 1
      · rw [sum_comm]
        exact sum_congr rfl fun p _ => (mul_sum _ _ _).symm
      · rw [sum_comm]
        refine sum_congr rfl fun p _ => ?_
        rw [sum_comm]
        exact sum_congr rfl fun q _ => (mul_sum _ _ _).symm
    have hdiag_ge : γ * Real.sqrt N * ∑ p ∈ P, α p ^ 2 ≤
        ∑ p ∈ P, α p ^ 2 * ∑ n ∈ S, centeredMultiple p n ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum fun p hp => ?_
      have hpP := Nat.prime_of_mem_primesLE hp
      have hpX : (p : ℝ) ≤ C₀ * Real.sqrt N :=
        (Nat.cast_le.mpr (Nat.le_of_mem_primesLE hp)).trans (Nat.floor_le (by positivity))
      have hmp := sum_centeredMultiple_sq_lateComb_ge_of_le_sqrt hC₀ hC0_sqrt_le hpP.two_le hpX
      calc γ * Real.sqrt N * α p ^ 2
          = α p ^ 2 * ((K : ℝ) / C₀ * Real.sqrt N) := by dsimp only [γ]; ring
        _ ≤ α p ^ 2 * ∑ n ∈ S, centeredMultiple p n ^ 2 :=
            mul_le_mul_of_nonneg_left hmp (sq_nonneg _)
    have hoff_le : |∑ p ∈ P, ∑ q ∈ P.erase p,
          α p * α q * ∑ n ∈ S, centeredMultiple p n * centeredMultiple q n| ≤
        (γ / 2) * Real.sqrt N * ∑ p ∈ P, α p ^ 2 := by
      calc |∑ p ∈ P, ∑ q ∈ P.erase p,
              α p * α q * ∑ n ∈ S, centeredMultiple p n * centeredMultiple q n|
          ≤ ∑ p ∈ P, ∑ q ∈ P.erase p,
              |α p * α q * ∑ n ∈ S, centeredMultiple p n * centeredMultiple q n| := by
            refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ => abs_sum_le_sum_abs _ _)
        _ ≤ ∑ p ∈ P, ∑ q ∈ P.erase p, |α p| * |α q| * 2 := by
            refine sum_le_sum fun p hp => sum_le_sum fun q hq => ?_
            obtain ⟨hqp, hqP⟩ := mem_erase.mp hq
            have hpP := Nat.prime_of_mem_primesLE hp
            have hqP' := Nat.prime_of_mem_primesLE hqP
            have hcop : Nat.Coprime p q := (Nat.coprime_primes hpP hqP').mpr hqp.symm
            rw [abs_mul, abs_mul]
            exact mul_le_mul_of_nonneg_left
              (abs_sum_centeredMultiple_mul_Ioc_le hpP.pos hqP'.pos hcop N (N + 3 * K * N))
              (by positivity)
        _ ≤ ∑ p ∈ P, ∑ q ∈ P, |α p| * |α q| * 2 :=
            sum_le_sum fun p _ => sum_le_sum_of_subset_of_nonneg (erase_subset p P)
              fun _ _ _ => by positivity
        _ = 2 * (∑ p ∈ P, |α p|) ^ 2 := by
            rw [sq, sum_mul, mul_sum]
            refine sum_congr rfl fun p _ => ?_
            rw [mul_sum, mul_sum]
            exact sum_congr rfl fun q _ => by ring
        _ ≤ 2 * ((P.card : ℝ) * ∑ p ∈ P, |α p| ^ 2) :=
            mul_le_mul_of_nonneg_left (sq_sum_le_card_mul_sum_sq P (fun p => |α p|)) (by norm_num)
        _ = (2 * (P.card : ℝ)) * ∑ p ∈ P, α p ^ 2 := by
            simp only [sq_abs]; ring
        _ ≤ (γ / 2) * Real.sqrt N * ∑ p ∈ P, α p ^ 2 :=
            mul_le_mul_of_nonneg_right hcard_le (sum_nonneg fun _ _ => sq_nonneg _)
    have hoff_low := (abs_le.mp hoff_le).1
    rw [hexp_c]
    linarith
  -- 4. Combine with controlled-cost positivity producer at `2 * κ`
  have hprod := hN₁ P id (fun _ => 0) α (fun p hp => (Nat.prime_of_mem_primesLE hp).pos)
  have hce : (fun n => ∑ p ∈ P, α p * centeredResidue p 0 n) = c := by
    funext n
    exact sum_congr rfl fun p hp => by
      rw [← centeredMultiple_eq_centeredResidue (Nat.prime_of_mem_primesLE hp).pos]
  rw [hce] at hprod
  have hcost_le : C₁ / (N : ℝ) * (∑ p ∈ P, |α p|) ^ 2 ≤ κ * ∑ n ∈ S, c n ^ 2 := by
    have hcs := sq_sum_le_card_mul_sum_sq P (fun p => |α p|)
    simp only [sq_abs] at hcs
    have hcard_C0 : (P.card : ℝ) ≤ C₀ * Real.sqrt N := by
      have hsub : P ⊆ Icc 1 X := fun p hp =>
        mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp).pos, Nat.le_of_mem_primesLE hp⟩
      calc (P.card : ℝ) ≤ ((Icc 1 X).card : ℝ) := by exact_mod_cast card_le_card hsub
        _ = (X : ℝ) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
        _ ≤ C₀ * Real.sqrt N := Nat.floor_le (by positivity)
    have hN_cost : 2 * C₁ * C₀ / (γ * κ) ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans
        (by exact_mod_cast (show ⌈2 * C₁ * C₀ / (γ * κ)⌉₊ ≤ N by dsimp only [N_min] at hN; omega))
    have hcoeff : 2 * C₁ * C₀ / (γ * (N : ℝ)) ≤ κ := by
      rw [div_le_iff₀ (by positivity)]
      exact ((div_le_iff₀ (by positivity : 0 < γ * κ)).mp hN_cost).trans_eq (by ring)
    calc C₁ / (N : ℝ) * (∑ p ∈ P, |α p|) ^ 2
        ≤ C₁ / (N : ℝ) * ((P.card : ℝ) * ∑ p ∈ P, α p ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ ≤ C₁ / (N : ℝ) * ((C₀ * Real.sqrt N) * ∑ p ∈ P, α p ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcard_C0 (sum_nonneg fun _ _ => sq_nonneg _))
            (by positivity)
      _ = (2 * C₁ * C₀ / (γ * (N : ℝ))) * ((γ / 2) * Real.sqrt N * ∑ p ∈ P, α p ^ 2) := by
          field_simp [hγ.ne', hN0.ne']; ring
      _ ≤ κ * ∑ n ∈ S, c n ^ 2 :=
          mul_le_mul hcoeff hgram (by positivity) hκ.le
  linarith

/-! ### Exact centered-divisibility spanning and the macroscopic cost barrier -/

private theorem sum_divisors_moebius_real (g : ℕ) :
    ∑ d ∈ g.divisors, (μ d : ℝ) = if g = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => (f g : ℝ))
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  push_cast at h
  exact h

private theorem abs_moebius_real_le_one (d : ℕ) : |(μ d : ℝ)| ≤ 1 := by
  have hint := ArithmeticFunction.abs_moebius_le_one (n := d)
  have hcast : |(μ d : ℝ)| = ((|μ d| : ℤ) : ℝ) := by push_cast; rfl
  rw [hcast]
  exact_mod_cast hint

/-- By Bertrand's postulate, a prime in `(Q / 2, Q]` divides a unique integer in `[1, Q]`,
so the finite Möbius harmonic sum `∑_{t=1}^Q μ(t) / t` never vanishes for `Q ≥ 2`. -/
theorem sum_moebius_div_Icc_ne_zero {Q : ℕ} (hQ : 2 ≤ Q) :
    ∑ t ∈ Icc 1 Q, (μ t : ℝ) / (t : ℝ) ≠ 0 := by
  obtain ⟨p, hp, hp_gt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul (Q / 2) (by omega)
  have hpQ : p ∈ Icc 1 Q := mem_Icc.mpr ⟨hp.pos, by omega⟩
  set E := (Icc 1 Q).erase p
  have honly : ∀ t ∈ E, ¬ p ∣ t := by
    rintro t ht ⟨k, rfl⟩
    obtain ⟨htp, htI⟩ := mem_erase.mp ht
    obtain ⟨ht1, htQ⟩ := mem_Icc.mp htI
    have hk0 : k ≠ 0 := by rintro rfl; omega
    have hk1 : k ≠ 1 := by rintro rfl; exact htp (mul_one p)
    have hk2 : 2 * p ≤ p * k := by nlinarith
    omega
  set L : ℕ := ∏ s ∈ E, s
  have hpL : ¬ p ∣ L := by
    intro hdvd
    obtain ⟨s, hs, hps⟩ := hp.prime.dvd_finset_prod_iff.mp hdvd
    exact honly s hs hps
  intro hzero
  have hp0R : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmul0 : (p : ℝ) * (L : ℝ) * ∑ t ∈ Icc 1 Q, (μ t : ℝ) / (t : ℝ) = 0 := by
    rw [hzero, mul_zero]
  rw [← insert_erase hpQ, sum_insert (not_mem_erase p _), mul_add] at hmul0
  have hterm_p : (p : ℝ) * (L : ℝ) * ((μ p : ℝ) / (p : ℝ)) = -((L : ℤ) : ℝ) := by
    rw [ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    field_simp [hp0R]
    ring
  have hterm_E : (p : ℝ) * (L : ℝ) * ∑ t ∈ E, (μ t : ℝ) / (t : ℝ) =
      (((p : ℤ) * ∑ t ∈ E, (μ t : ℤ) * ((L / t : ℕ) : ℤ)) : ℝ) := by
    rw [mul_sum]
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun t ht => ?_
    have ht0 : 0 < t := (mem_Icc.mp (mem_of_mem_erase ht)).1
    have ht0R : (t : ℝ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hdvd : t ∣ L := dvd_prod_of_mem id ht
    have hL_eq : (L : ℝ) = (t : ℝ) * ((L / t : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
    rw [hL_eq]
    field_simp [ht0R]
    ring
  rw [hterm_p, hterm_E] at hmul0
  have hInt_eq : ((L : ℤ) : ℝ) = (((p : ℤ) * ∑ t ∈ E, (μ t : ℤ) * ((L / t : ℕ) : ℤ)) : ℝ) := by
    linarith
  have hInt := Int.cast_injective hInt_eq
  have hdvdZ : (p : ℤ) ∣ (L : ℤ) := ⟨∑ t ∈ E, (μ t : ℤ) * ((L / t : ℕ) : ℤ), hInt⟩
  exact hpL (Int.ofNat_dvd.mp hdvdZ)

/-- **Exact centered-divisibility spanning at macroscopic cost.** For every ratio bound
`Q ≥ 2` there is `C_Q > 0` (independent of `N`) such that for every `N ≥ 2` and every
real vector `c : ℕ → ℝ`, some coefficient vector `α` represents `c` identically on
`Ioc N (QN)` as `∑_{d=2}^{QN} α_d v_d` with `(∑_{d=2}^{QN} |α_d|)^2 ≤ C_Q N ∑_{n ∈ Ioc N (QN)} c(n)^2`. -/
theorem exists_centeredMultiple_comb_representation {Q : ℕ} (hQ : 2 ≤ Q) :
    ∃ C_Q : ℝ, 0 < C_Q ∧ ∀ {N : ℕ}, 2 ≤ N → ∀ c : ℕ → ℝ,
      ∃ α : ℕ → ℝ,
        (∀ n ∈ Ioc N (Q * N),
          c n = ∑ d ∈ Icc 2 (Q * N), α d * centeredMultiple d n) ∧
        (∑ d ∈ Icc 2 (Q * N), |α d|) ^ 2 ≤
          C_Q * (N : ℝ) * ∑ n ∈ Ioc N (Q * N), c n ^ 2 := by
  set μ_Q : ℝ := ∑ t ∈ Icc 1 Q, (μ t : ℝ) / (t : ℝ)
  have hμQ_ne : μ_Q ≠ 0 := sum_moebius_div_Icc_ne_zero hQ
  have hμQ_abs : 0 < |μ_Q| := abs_pos.mpr hμQ_ne
  set C_Q : ℝ := ((Q : ℝ) + (Q : ℝ) ^ 2 / |μ_Q|) ^ 2 * (Q : ℝ) + 1
  refine ⟨C_Q, by positivity, fun {N} hN c => ?_⟩
  set S := Ioc N (Q * N)
  set D := Icc 2 (Q * N)
  let γ : ℕ → ℝ := fun m => (1 / (m : ℝ)) * ∑ j ∈ Icc 1 ((Q * N) / m), (μ j : ℝ) / (j : ℝ)
  let β : ℝ := (∑ m ∈ S, c m * γ m) * (N : ℝ) / μ_Q
  let α : ℕ → ℝ := fun d =>
    (∑ m ∈ S, ∑ j ∈ (Icc 1 ((Q * N) / m)).filter (fun j => j * m = d), c m * (μ j : ℝ)) -
      β * ∑ t ∈ (Icc 1 Q).filter (fun t => t * N = d), (μ t : ℝ)
  have hmaps1 : ∀ m ∈ S, ∀ j ∈ Icc 1 ((Q * N) / m), j * m ∈ D := fun m hm j hj => by
    obtain ⟨hmN, _⟩ := mem_Ioc.mp hm
    obtain ⟨hj1, hjtop⟩ := mem_Icc.mp hj
    have hm0 : 0 < m := by omega
    refine mem_Icc.mpr ⟨by nlinarith, ?_⟩
    rw [mul_comm]
    exact (Nat.le_div_iff_mul_le hm0).mp hjtop
  have hmaps2 : ∀ t ∈ Icc 1 Q, t * N ∈ D := fun t ht => by
    obtain ⟨ht1, htQ⟩ := mem_Icc.mp ht
    exact mem_Icc.mpr ⟨by nlinarith, Nat.mul_le_mul_right N htQ⟩
  refine ⟨α, fun n hn => ?_, ?_⟩
  · -- Pointwise exact representation on `S`
    have hfib1 : ∀ m ∈ S,
        ∑ d ∈ D, (∑ j ∈ (Icc 1 ((Q * N) / m)).filter (fun j => j * m = d), c m * (μ j : ℝ)) *
            centeredMultiple d n =
          c m * ∑ j ∈ Icc 1 ((Q * N) / m), (μ j : ℝ) * centeredMultiple (j * m) n := by
      intro m hm
      have h1 : ∀ d ∈ D,
          (∑ j ∈ (Icc 1 ((Q * N) / m)).filter (fun j => j * m = d), c m * (μ j : ℝ)) *
              centeredMultiple d n =
            ∑ j ∈ (Icc 1 ((Q * N) / m)).filter (fun j => j * m = d),
              c m * ((μ j : ℝ) * centeredMultiple (j * m) n) := by
        intro d _
        rw [sum_mul]
        exact sum_congr rfl fun j hj => by rw [(mem_filter.mp hj).2]; ring
      rw [sum_congr rfl h1, sum_fiberwise_of_maps_to (hmaps1 m hm), ← mul_sum]
    have hfib2 : ∑ d ∈ D, (∑ t ∈ (Icc 1 Q).filter (fun t => t * N = d), (μ t : ℝ)) *
          centeredMultiple d n =
        ∑ t ∈ Icc 1 Q, (μ t : ℝ) * centeredMultiple (t * N) n := by
      have h1 : ∀ d ∈ D,
          (∑ t ∈ (Icc 1 Q).filter (fun t => t * N = d), (μ t : ℝ)) * centeredMultiple d n =
            ∑ t ∈ (Icc 1 Q).filter (fun t => t * N = d), (μ t : ℝ) * centeredMultiple (t * N) n := by
        intro d _
        rw [sum_mul]
        exact sum_congr rfl fun t ht => by rw [(mem_filter.mp ht).2]
      rw [sum_congr rfl h1, sum_fiberwise_of_maps_to hmaps2]
    have hexp_d : ∑ d ∈ D, α d * centeredMultiple d n =
        (∑ m ∈ S, c m * ∑ j ∈ Icc 1 ((Q * N) / m), (μ j : ℝ) * centeredMultiple (j * m) n) -
          β * ∑ t ∈ Icc 1 Q, (μ t : ℝ) * centeredMultiple (t * N) n := by
      dsimp only [α]
      simp only [sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum]
      rw [← hfib2]
      congr 1
      have hswap : (∑ d ∈ D,
            (∑ m ∈ S, ∑ j ∈ (Icc 1 ((Q * N) / m)).filter (fun j => j * m = d), c m * (μ j : ℝ)) *
              centeredMultiple d n) =
          ∑ m ∈ S, ∑ d ∈ D,
            (∑ j ∈ (Icc 1 ((Q * N) / m)).filter (fun j => j * m = d), c m * (μ j : ℝ)) *
              centeredMultiple d n := by
        simp only [sum_mul]
        exact sum_comm
      rw [hswap, sum_congr rfl hfib1]
    -- Evaluate the upper-triangular Möbius delta sum for `m, n ∈ S`
    have hdelta : ∀ m ∈ S,
        ∑ j ∈ Icc 1 ((Q * N) / m), (μ j : ℝ) * centeredMultiple (j * m) n =
          (if m = n then 1 else 0) - γ m := by
      intro m hm
      obtain ⟨hmN, _⟩ := mem_Ioc.mp hm
      obtain ⟨hnN, hnQN⟩ := mem_Ioc.mp hn
      have hm0 : 0 < m := by omega
      have hsplit : ∑ j ∈ Icc 1 ((Q * N) / m), (μ j : ℝ) * centeredMultiple (j * m) n =
          (∑ j ∈ Icc 1 ((Q * N) / m), (μ j : ℝ) * (if j * m ∣ n then 1 else 0)) - γ m := by
        dsimp only [γ]
        rw [mul_sum, ← sum_sub_distrib]
        refine sum_congr rfl fun j _ => ?_
        rw [centeredMultiple, Nat.cast_mul]
        simp only [one_div, div_eq_mul_inv, mul_inv]
        ring
      rw [hsplit]
      congr 1
      by_cases hmn_dvd : m ∣ n
      · obtain ⟨k, rfl⟩ := hmn_dvd
        have hk0 : 0 < k := by rcases Nat.eq_zero_or_pos k with rfl | hk; · omega; · exact hk
        have hktop : k ≤ (Q * N) / m :=
          (Nat.le_div_iff_mul_le hm0).mpr (by rw [mul_comm]; exact hnQN)
        have hiff_j : ∀ j : ℕ, (j * m ∣ m * k) ↔ j ∣ k := fun j => by
          rw [mul_comm j m]
          exact mul_dvd_mul_iff_left hm0.ne'
        have hfilt : (Icc 1 ((Q * N) / m)).filter (· ∣ k) = k.divisors := by
          ext j
          simp only [mem_filter, mem_Icc, Nat.mem_divisors]
          constructor
          · rintro ⟨_, hjk⟩; exact ⟨hjk, hk0.ne'⟩
          · rintro ⟨hjk, _⟩
            exact ⟨⟨Nat.pos_of_dvd_of_pos hjk hk0, (Nat.le_of_dvd hk0 hjk).trans hktop⟩, hjk⟩
        have hsum_k : (∑ j ∈ Icc 1 ((Q * N) / m), (μ j : ℝ) * (if j * m ∣ m * k then 1 else 0)) =
            ∑ j ∈ k.divisors, (μ j : ℝ) := by
          rw [← hfilt, sum_filter]
          refine sum_congr rfl fun j _ => ?_
          rw [hiff_j]
          split_ifs <;> ring
        rw [hsum_k, sum_divisors_moebius_real k]
        have hk1_iff : (k = 1) ↔ (m = m * k) := by
          constructor
          · rintro rfl; rw [mul_one]
          · intro h; exact (Nat.eq_of_mul_eq_mul_left hm0 (h.symm.trans (mul_one m).symm))
        by_cases hk1 : k = 1
        · rw [if_pos hk1, if_pos (hk1_iff.mp hk1)]
        · rw [if_neg hk1, if_neg (mt hk1_iff.mpr hk1)]
      · have hno : ∀ j ∈ Icc 1 ((Q * N) / m), ¬ (j * m ∣ n) := fun j _ hjm =>
          hmn_dvd (dvd_trans (dvd_mul_left m j) hjm)
        have hz : (∑ j ∈ Icc 1 ((Q * N) / m), (μ j : ℝ) * (if j * m ∣ n then 1 else 0)) = 0 :=
          sum_eq_zero fun j hj => by rw [if_neg (hno j hj), mul_zero]
        have hne : m ≠ n := fun h => hmn_dvd (h ▸ dvd_refl m)
        rw [hz, if_neg hne]
    -- Evaluate the constant-synthesizing sum `t * N` for `n ∈ S`
    have hconst_N : ∑ t ∈ Icc 1 Q, (μ t : ℝ) * centeredMultiple (t * N) n = -μ_Q / (N : ℝ) := by
      obtain ⟨hnN, hnQN⟩ := mem_Ioc.mp hn
      have hN0 : 0 < N := by omega
      have hsplit : ∑ t ∈ Icc 1 Q, (μ t : ℝ) * centeredMultiple (t * N) n =
          (∑ t ∈ Icc 1 Q, (μ t : ℝ) * (if t * N ∣ n then 1 else 0)) - μ_Q / (N : ℝ) := by
        dsimp only [μ_Q]
        rw [sum_div, ← sum_sub_distrib]
        refine sum_congr rfl fun t _ => ?_
        rw [centeredMultiple, Nat.cast_mul]
        simp only [one_div, div_eq_mul_inv, mul_inv]
        ring
      rw [hsplit]
      suffices hz : (∑ t ∈ Icc 1 Q, (μ t : ℝ) * (if t * N ∣ n then 1 else 0)) = 0 by
        rw [hz, zero_sub]
      by_cases hNdvd : N ∣ n
      · obtain ⟨k, rfl⟩ := hNdvd
        have hk2 : 2 ≤ k := by
          rcases k with _ | _ | k
          · simp at hnN
          · rw [mul_one] at hnN; omega
          · omega
        have hkQ : k ≤ Q := Nat.le_of_mul_le_mul_right (by rw [mul_comm]; exact hnQN) hN0
        have hiff_t : ∀ t : ℕ, (t * N ∣ N * k) ↔ t ∣ k := fun t => by
          rw [mul_comm t N]
          exact mul_dvd_mul_iff_left hN0.ne'
        have hfilt : (Icc 1 Q).filter (· ∣ k) = k.divisors := by
          ext t
          simp only [mem_filter, mem_Icc, Nat.mem_divisors]
          constructor
          · rintro ⟨_, htk⟩; exact ⟨htk, by omega⟩
          · rintro ⟨htk, _⟩
            exact ⟨⟨Nat.pos_of_dvd_of_pos htk (by omega),
              (Nat.le_of_dvd (by omega) htk).trans hkQ⟩, htk⟩
        have hsum_k : (∑ t ∈ Icc 1 Q, (μ t : ℝ) * (if t * N ∣ N * k then 1 else 0)) =
            ∑ t ∈ k.divisors, (μ t : ℝ) := by
          rw [← hfilt, sum_filter]
          refine sum_congr rfl fun t _ => ?_
          rw [hiff_t]
          split_ifs <;> ring
        rw [hsum_k, sum_divisors_moebius_real k, if_neg (by omega)]
      · exact sum_eq_zero fun t _ => by
          have hno : ¬ (t * N ∣ n) := fun htN => hNdvd (dvd_trans (dvd_mul_left N t) htN)
          rw [if_neg hno, mul_zero]
    have hsum_delta :
        (∑ m ∈ S, c m * ∑ j ∈ Icc 1 ((Q * N) / m), (μ j : ℝ) * centeredMultiple (j * m) n) =
          ∑ m ∈ S, c m * ((if m = n then 1 else 0) - γ m) :=
      sum_congr rfl fun m hm => by rw [hdelta m hm]
    rw [hexp_d, hsum_delta, hconst_N]
    have hite : ∑ m ∈ S, c m * ((if m = n then (1 : ℝ) else 0) - γ m) =
        c n - ∑ m ∈ S, c m * γ m := by
      simp only [mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero, sum_ite_eq', hn, if_true]
    have hN0R : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [hite]
    dsimp only [β]
    have hcancel : (∑ m ∈ S, c m * γ m) * (N : ℝ) / μ_Q * (-μ_Q / (N : ℝ)) =
        -(∑ m ∈ S, c m * γ m) := by
      field_simp [hμQ_ne, hN0R]; ring
    linarith
  · -- Macroscopic `ℓ^1` cost bound `(∑ |α_d|)^2 ≤ C_Q * N * ∑_{n ∈ S} c(n)^2`
    have hN0R : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hγ_le : ∀ m ∈ S, |γ m| ≤ (Q : ℝ) / (N : ℝ) := by
      intro m hm
      obtain ⟨hmN, _⟩ := mem_Ioc.mp hm
      have hm0R : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have htopQ : (Q * N) / m ≤ Q := by
        apply Nat.div_le_of_le_mul
        nlinarith
      dsimp only [γ]
      rw [abs_mul, abs_of_pos (by positivity)]
      have hsum_j : |∑ j ∈ Icc 1 ((Q * N) / m), (μ j : ℝ) / (j : ℝ)| ≤ (Q : ℝ) := by
        calc |∑ j ∈ Icc 1 ((Q * N) / m), (μ j : ℝ) / (j : ℝ)|
            ≤ ∑ j ∈ Icc 1 ((Q * N) / m), |(μ j : ℝ) / (j : ℝ)| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ _j ∈ Icc 1 ((Q * N) / m), (1 : ℝ) := by
              refine sum_le_sum fun j hj => ?_
              have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (mem_Icc.mp hj).1
              rw [abs_div, abs_of_pos (by positivity)]
              exact div_le_one_of_le₀ ((abs_moebius_real_le_one j).trans hj1) (by positivity)
          _ = (((Q * N) / m : ℕ) : ℝ) := by rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
          _ ≤ (Q : ℝ) := by exact_mod_cast htopQ
      calc (1 / (m : ℝ)) * |∑ j ∈ Icc 1 ((Q * N) / m), (μ j : ℝ) / (j : ℝ)|
          ≤ (1 / (N : ℝ)) * (Q : ℝ) :=
            mul_le_mul (one_div_le_one_div_of_le hN0R (by exact_mod_cast hmN.le))
              hsum_j (abs_nonneg _) (by positivity)
        _ = (Q : ℝ) / (N : ℝ) := by ring
    have hβ_le : |β| ≤ ((Q : ℝ) / |μ_Q|) * ∑ m ∈ S, |c m| := by
      dsimp only [β]
      rw [abs_div, abs_mul, abs_of_pos hN0R]
      have hcm : |∑ m ∈ S, c m * γ m| ≤ ((Q : ℝ) / (N : ℝ)) * ∑ m ∈ S, |c m| := by
        calc |∑ m ∈ S, c m * γ m|
            ≤ ∑ m ∈ S, |c m * γ m| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ m ∈ S, |c m| * ((Q : ℝ) / (N : ℝ)) := by
              refine sum_le_sum fun m hm => ?_
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (hγ_le m hm) (abs_nonneg _)
          _ = ((Q : ℝ) / (N : ℝ)) * ∑ m ∈ S, |c m| := by rw [← sum_mul, mul_comm]
      calc |∑ m ∈ S, c m * γ m| * (N : ℝ) / |μ_Q|
          ≤ (((Q : ℝ) / (N : ℝ)) * ∑ m ∈ S, |c m|) * (N : ℝ) / |μ_Q| :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcm hN0R.le) hμQ_abs.le
        _ = ((Q : ℝ) / |μ_Q|) * ∑ m ∈ S, |c m| := by
            field_simp [hN0R.ne', hμQ_abs.ne']; ring
    have hsum_α : ∑ d ∈ D, |α d| ≤ ((Q : ℝ) + (Q : ℝ) ^ 2 / |μ_Q|) * ∑ m ∈ S, |c m| := by
      have hpart1 : ∑ d ∈ D,
            |∑ m ∈ S, ∑ j ∈ (Icc 1 ((Q * N) / m)).filter (fun j => j * m = d), c m * (μ j : ℝ)| ≤
          (Q : ℝ) * ∑ m ∈ S, |c m| := by
        calc ∑ d ∈ D,
              |∑ m ∈ S, ∑ j ∈ (Icc 1 ((Q * N) / m)).filter (fun j => j * m = d), c m * (μ j : ℝ)|
            ≤ ∑ d ∈ D, ∑ m ∈ S,
                ∑ j ∈ (Icc 1 ((Q * N) / m)).filter (fun j => j * m = d), |c m * (μ j : ℝ)| :=
              sum_le_sum fun d _ => (abs_sum_le_sum_abs _ _).trans
                (sum_le_sum fun m _ => abs_sum_le_sum_abs _ _)
          _ = ∑ m ∈ S, ∑ d ∈ D,
                ∑ j ∈ (Icc 1 ((Q * N) / m)).filter (fun j => j * m = d), |c m * (μ j : ℝ)| := sum_comm
          _ = ∑ m ∈ S, ∑ j ∈ Icc 1 ((Q * N) / m), |c m * (μ j : ℝ)| :=
              sum_congr rfl fun m hm => sum_fiberwise_of_maps_to (hmaps1 m hm) _
          _ ≤ ∑ m ∈ S, (Q : ℝ) * |c m| := by
              refine sum_le_sum fun m hm => ?_
              obtain ⟨hmN, _⟩ := mem_Ioc.mp hm
              have htopQ : (Q * N) / m ≤ Q := Nat.div_le_of_le_mul (by nlinarith)
              calc ∑ j ∈ Icc 1 ((Q * N) / m), |c m * (μ j : ℝ)|
                  ≤ ∑ _j ∈ Icc 1 ((Q * N) / m), |c m| := by
                    refine sum_le_sum fun j _ => ?_
                    rw [abs_mul]
                    simpa using mul_le_mul_of_nonneg_left (abs_moebius_real_le_one j) (abs_nonneg _)
                _ = (((Q * N) / m : ℕ) : ℝ) * |c m| := by
                    rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
                _ ≤ (Q : ℝ) * |c m| := mul_le_mul_of_nonneg_right (by exact_mod_cast htopQ) (abs_nonneg _)
          _ = (Q : ℝ) * ∑ m ∈ S, |c m| := (mul_sum _ _ _).symm
      have hpart2 : ∑ d ∈ D, |β * ∑ t ∈ (Icc 1 Q).filter (fun t => t * N = d), (μ t : ℝ)| ≤
          ((Q : ℝ) ^ 2 / |μ_Q|) * ∑ m ∈ S, |c m| := by
        calc ∑ d ∈ D, |β * ∑ t ∈ (Icc 1 Q).filter (fun t => t * N = d), (μ t : ℝ)|
            ≤ ∑ d ∈ D, |β| * ∑ t ∈ (Icc 1 Q).filter (fun t => t * N = d), |(μ t : ℝ)| :=
              sum_le_sum fun d _ => by
                rw [abs_mul]
                exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (abs_nonneg _)
          _ = |β| * ∑ d ∈ D, ∑ t ∈ (Icc 1 Q).filter (fun t => t * N = d), |(μ t : ℝ)| :=
              (mul_sum _ _ _).symm
          _ = |β| * ∑ t ∈ Icc 1 Q, |(μ t : ℝ)| := by
              rw [sum_fiberwise_of_maps_to hmaps2]
          _ ≤ |β| * (Q : ℝ) := by
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              calc ∑ t ∈ Icc 1 Q, |(μ t : ℝ)| ≤ ∑ _t ∈ Icc 1 Q, (1 : ℝ) :=
                    sum_le_sum fun t _ => abs_moebius_real_le_one t
                _ = (Q : ℝ) := by rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
          _ ≤ (((Q : ℝ) / |μ_Q|) * ∑ m ∈ S, |c m|) * (Q : ℝ) :=
              mul_le_mul_of_nonneg_right hβ_le (Nat.cast_nonneg Q)
          _ = ((Q : ℝ) ^ 2 / |μ_Q|) * ∑ m ∈ S, |c m| := by ring
      calc ∑ d ∈ D, |α d|
          ≤ ∑ d ∈ D,
              (|∑ m ∈ S, ∑ j ∈ (Icc 1 ((Q * N) / m)).filter (fun j => j * m = d), c m * (μ j : ℝ)| +
                |β * ∑ t ∈ (Icc 1 Q).filter (fun t => t * N = d), (μ t : ℝ)|) :=
            sum_le_sum fun d _ => abs_sub _ _
        _ = (∑ d ∈ D, |∑ m ∈ S, ∑ j ∈ (Icc 1 ((Q * N) / m)).filter (fun j => j * m = d), c m * (μ j : ℝ)|) +
              ∑ d ∈ D, |β * ∑ t ∈ (Icc 1 Q).filter (fun t => t * N = d), (μ t : ℝ)| :=
            sum_add_distrib
        _ ≤ (Q : ℝ) * (∑ m ∈ S, |c m|) + ((Q : ℝ) ^ 2 / |μ_Q|) * ∑ m ∈ S, |c m| :=
            add_le_add hpart1 hpart2
        _ = ((Q : ℝ) + (Q : ℝ) ^ 2 / |μ_Q|) * ∑ m ∈ S, |c m| := by ring
    have hcs_S := sq_sum_le_card_mul_sum_sq S (fun m => |c m|)
    simp only [sq_abs] at hcs_S
    have hcardS : (S.card : ℝ) ≤ (Q : ℝ) * N := by
      dsimp only [S]
      rw [Nat.card_Ioc]
      have : Q * N - N ≤ Q * N := Nat.sub_le _ _
      exact_mod_cast this
    calc (∑ d ∈ D, |α d|) ^ 2
        ≤ (((Q : ℝ) + (Q : ℝ) ^ 2 / |μ_Q|) * ∑ m ∈ S, |c m|) ^ 2 :=
          pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) hsum_α 2
      _ = ((Q : ℝ) + (Q : ℝ) ^ 2 / |μ_Q|) ^ 2 * (∑ m ∈ S, |c m|) ^ 2 := by ring
      _ ≤ ((Q : ℝ) + (Q : ℝ) ^ 2 / |μ_Q|) ^ 2 * ((S.card : ℝ) * ∑ m ∈ S, c m ^ 2) :=
          mul_le_mul_of_nonneg_left hcs_S (sq_nonneg _)
      _ ≤ ((Q : ℝ) + (Q : ℝ) ^ 2 / |μ_Q|) ^ 2 * (((Q : ℝ) * N) * ∑ m ∈ S, c m ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcardS (sum_nonneg fun _ _ => sq_nonneg _))
            (sq_nonneg _)
      _ ≤ C_Q * (N : ℝ) * ∑ n ∈ S, c n ^ 2 := by
          dsimp only [C_Q]
          have hnn : 0 ≤ (N : ℝ) * ∑ n ∈ S, c n ^ 2 :=
            mul_nonneg hN0R.le (sum_nonneg fun _ _ => sq_nonneg _)
          nlinarith

/-! ### Unconditional Liouville-twin refutation at macroscopic cost and exact RH equivalences -/

private theorem combFormW_liouville_eq_pencilCombForm_of_lt_three
    {A B : ℕ} (hB : B < 3 * A) (c : ℕ → ℝ) :
    combFormW SelectiveArithmetic.liouvilleWeight (Ioc A B) c =
      GreenCalculusOfThePrimeFreeWindow.pencilCombForm (-1) (Ioc A B) c := by
  set W := Ioc A B
  rw [combFormW_eq, GreenCalculusOfThePrimeFreeWindow.pencilCombForm]
  have hcont : ∑ n ∈ W, ∑ m ∈ W.erase n,
        c m * c n * contactW (fun k => SelectiveArithmetic.liouvilleWeight k - Λ k) m n =
      -(4 * Real.log 2 * GreenCalculusOfThePrimeFreeWindow.doubleContact W c) := by
    have hone : (∑ n ∈ W, ∑ m ∈ W.erase n, c m * c n *
          (if m ∣ n then SelectiveArithmetic.liouvilleWeight (n / m) - (Λ (n / m) : ℝ) else 0)) =
        -(2 * Real.log 2) * GreenCalculusOfThePrimeFreeWindow.doubleContact W c := by
      rw [Finset.sum_comm' (s' := fun m => W.erase m) (t' := W) (fun n m => by
        simp only [mem_erase]; tauto)]
      unfold GreenCalculusOfThePrimeFreeWindow.doubleContact
      rw [mul_sum]
      refine sum_congr rfl fun m hm => ?_
      obtain ⟨hmA, _⟩ := mem_Ioc.mp hm
      by_cases h2m : 2 * m ∈ W
      · rw [if_pos h2m]
        have hmem_er : 2 * m ∈ W.erase m := mem_erase.mpr ⟨by omega, h2m⟩
        rw [sum_eq_single (2 * m)]
        · have hdiv2 : 2 * m / m = 2 := Nat.mul_div_cancel 2 (by omega)
          have h2notSq : ¬ IsSquare (2 : ℕ) := by
            rintro ⟨k, hk⟩
            rcases k with _ | _ | k
            · omega
            · omega
            · nlinarith
          rw [if_pos (dvd_mul_left m 2), hdiv2]
          unfold SelectiveArithmetic.liouvilleWeight
          rw [if_neg h2notSq, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
          norm_num
          ring
        · intro n hnE hn2m
          by_cases hdvd : m ∣ n
          · obtain ⟨r, rfl⟩ := hdvd
            obtain ⟨hne, hnW⟩ := mem_erase.mp hnE
            obtain ⟨hnA, hnB⟩ := mem_Ioc.mp hnW
            have hr0 : r ≠ 0 := by rintro rfl; simp at hnA
            have hr1 : r ≠ 1 := by rintro rfl; exact hne (mul_one m)
            have hr2 : r ≠ 2 := fun hr2 => hn2m (by rw [hr2]; ring)
            exfalso
            have hmr : 3 * (A + 1) ≤ m * r := by
              rw [mul_comm]; exact Nat.mul_le_mul (by omega) hmA
            linarith
          · simp [hdvd]
        · intro hnot; exact False.elim (hnot hmem_er)
      · rw [if_neg h2m, mul_zero]
        refine sum_eq_zero fun n hnE => ?_
        by_cases hdvd : m ∣ n
        · obtain ⟨r, rfl⟩ := hdvd
          obtain ⟨hne, hnW⟩ := mem_erase.mp hnE
          obtain ⟨hnA, hnB⟩ := mem_Ioc.mp hnW
          have hr0 : r ≠ 0 := by rintro rfl; simp at hnA
          have hr1 : r ≠ 1 := by rintro rfl; exact hne (mul_one m)
          have hr2 : r ≠ 2 := fun hr2 => h2m (by rw [← hr2, mul_comm]; exact hnW)
          exfalso
          have hmr : 3 * (A + 1) ≤ m * r := by
            rw [mul_comm]; exact Nat.mul_le_mul (by omega) hmA
          linarith
        · simp [hdvd]
    have hsplit : (∑ n ∈ W, ∑ m ∈ W.erase n,
          c m * c n * contactW (fun k => SelectiveArithmetic.liouvilleWeight k - Λ k) m n) =
        2 * ∑ n ∈ W, ∑ m ∈ W.erase n, c m * c n *
          (if m ∣ n then SelectiveArithmetic.liouvilleWeight (n / m) - (Λ (n / m) : ℝ) else 0) := by
      simp only [contactW, mul_add, sum_add_distrib]
      rw [two_mul]
      congr 1
      exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
    rw [hsplit, hone]
    ring
  rw [hcont]
  ring

/-- **Unconditional Liouville-twin refutation at macroscopic cost.** For every comb
width `K ≥ 1`, there is `C > 0` such that eventually in `N`, some linear combination
`c = ∑_{d=2}^{(1+3K)N} α_d v_d` of macroscopic cost `(∑ |α_d|)^2 ≤ C N ∑_{n ∈ S} c(n)^2`
and positive `ℓ^2` mass on `S = Ioc N (N + 3KN)` has
`combFormW SelectiveArithmetic.liouvilleWeight S c < -(1 / 2000) ∑_{n ∈ S} c(n)^2 < 0`
(equivalently `diagRealBudget S c < mixedPrimeDebitW SelectiveArithmetic.liouvilleWeight S c`). -/
theorem eventually_exists_liouville_centeredMultiple_neg {K : ℕ} (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∃ α : ℕ → ℝ,
        let S := Ioc N (N + 3 * K * N)
        let c := fun n => ∑ d ∈ Icc 2 ((1 + 3 * K) * N), α d * centeredMultiple d n
        0 < ∑ n ∈ S, c n ^ 2 ∧
        (∑ d ∈ Icc 2 ((1 + 3 * K) * N), |α d|) ^ 2 ≤ C * (N : ℝ) * ∑ n ∈ S, c n ^ 2 ∧
        combFormW SelectiveArithmetic.liouvilleWeight S c <
          -(1 / 2000) * ∑ n ∈ S, c n ^ 2 ∧
        diagRealBudget S c <
          mixedPrimeDebitW SelectiveArithmetic.liouvilleWeight S c := by
  obtain ⟨C_span, hC_span, hspan⟩ :=
    exists_centeredMultiple_comb_representation (Q := 1 + 3 * K) (by omega)
  obtain ⟨R, J, hR, hwin, σ, hσ⟩ :=
    GreenCalculusOfThePrimeFreeWindow.exists_window_signTwin_pencil_lt
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  -- Deduce `5000 * (R + J) < 10609 * R`, hence `R + J < 3 * R`
  have hlog : (2 * (37 / 100) : ℝ) ≤ Real.log (10609 / 5000) := by
    have h1 : Real.log (10609 / 5000 : ℝ) = Real.log 2 + Real.log (10609 / 10000) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; congr 1; norm_num
    have h2 := Real.log_two_gt_d9
    have h3 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 10609 / 10000 by norm_num)
    have h4 : (1 : ℝ) - (10609 / 10000)⁻¹ = 609 / 10609 := by norm_num
    rw [h4] at h3; rw [h1]; linarith
  have hpos_RJ : (0 : ℝ) < ((R + J : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < R + J)
  have hlt_log : Real.log ((R + J : ℕ) : ℝ) < Real.log (10609 / 5000 * R) := by
    rw [Real.log_mul (by norm_num) hR'.ne']; linarith
  have hlt_real : ((R + J : ℕ) : ℝ) < 10609 / 5000 * R :=
    (Real.log_lt_log_iff hpos_RJ (mul_pos (by norm_num) hR')).mp hlt_log
  have hnat5000 : 5000 * (R + J) < 10609 * R := by
    have h5 : (5000 : ℝ) * ((R + J : ℕ) : ℝ) < 10609 * R := by linarith
    exact_mod_cast h5
  have hJ3_lt : R + J < 3 * R := by omega
  -- Convergence of `pencilCombForm (-1)` along even block sizes `2 * b`
  have htend_2b : Tendsto (fun b : ℕ => 2 * b) atTop atTop :=
    tendsto_atTop_mono (fun b => Nat.le_mul_of_pos_left b (by norm_num)) tendsto_id
  have htend_comb := (tendsto_combForm_blockFunction_div hR hJ3_lt.le σ).comp htend_2b
  have htend_pen : Tendsto
      (fun b : ℕ =>
        GreenCalculusOfThePrimeFreeWindow.pencilCombForm (-1)
          (Ioc (R * (2 * b)) (R * (2 * b) + 2 * b * J))
          (fun n => σ (blockIndex (R * (2 * b)) (2 * b) n)) / ((2 * b : ℕ) : ℝ))
      atTop (𝓝 (GreenCalculusOfThePrimeFreeWindow.pencilStepForm (-1) 3 R J σ)) := by
    have hconst : Tendsto
        (fun _b : ℕ => (1 - (-1 : ℝ)) *
          ∑ j ∈ range J, ∑ l ∈ range J,
            σ j * σ l * GreenCalculusOfThePrimeFreeWindow.floorGraph 2 (R + j) (R + l))
        atTop
        (𝓝 ((1 - (-1 : ℝ)) *
          ∑ j ∈ range J, ∑ l ∈ range J,
            σ j * σ l * GreenCalculusOfThePrimeFreeWindow.floorGraph 2 (R + j) (R + l))) :=
      tendsto_const_nhds
    refine (htend_comb.add hconst).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with b hb1
    have hb0R : ((2 * b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show 2 * b ≠ 0 by omega)
    dsimp only [Function.comp_def]
    rw [GreenCalculusOfThePrimeFreeWindow.pencilCombForm, add_div, mul_div_assoc,
      GreenCalculusOfThePrimeFreeWindow.two_log_two_mul_doubleContact_blockFunction hR hb1 J σ,
      mul_div_cancel_left₀ _ hb0R]
  have hσ_pos : 0 < ∑ j ∈ range J, σ j ^ 2 := by
    by_contra hle
    have hz_sum : ∑ j ∈ range J, σ j ^ 2 = 0 :=
      le_antisymm (not_lt.mp hle) (sum_nonneg fun _ _ => sq_nonneg _)
    have hz_pt : ∀ j ∈ range J, σ j = 0 := fun j hj => by
      have hsq0 : σ j ^ 2 = 0 :=
        le_antisymm (single_le_sum (fun _ _ => sq_nonneg _) hj |>.trans_eq hz_sum) (sq_nonneg _)
      exact sq_eq_zero_iff.mp hsq0
    -- At `b ≥ 1`, `σ (blockIndex ...) = 0` on the entire window, so `pencilCombForm = 0`
    have hev0 : ∀ᶠ b : ℕ in atTop,
        GreenCalculusOfThePrimeFreeWindow.pencilCombForm (-1)
          (Ioc (R * (2 * b)) (R * (2 * b) + 2 * b * J))
          (fun n => σ (blockIndex (R * (2 * b)) (2 * b) n)) / ((2 * b : ℕ) : ℝ) = 0 := by
      filter_upwards [eventually_ge_atTop 1] with b hb1
      set Wb := Ioc (R * (2 * b)) (R * (2 * b) + 2 * b * J)
      have hg0 : ∀ n ∈ Wb, σ (blockIndex (R * (2 * b)) (2 * b) n) = 0 := by
        intro n hn
        apply hz_pt
        rw [mem_range]
        obtain ⟨hn1, hn2⟩ := mem_Ioc.mp hn
        by_contra hge
        have hmul := Nat.mul_le_mul_left (2 * b) (not_lt.mp hge)
        have ⟨hb_low, _⟩ := blockIndex_bounds (show 0 < 2 * b by omega) hn1
        omega
      have hc0 : combForm Wb (fun n => σ (blockIndex (R * (2 * b)) (2 * b) n)) = 0 := by
        rw [combForm_congr hg0]
        simp [combForm, combPairing, degOne, degTwo]
      have hd0 : GreenCalculusOfThePrimeFreeWindow.doubleContact Wb
          (fun n => σ (blockIndex (R * (2 * b)) (2 * b) n)) = 0 :=
        sum_eq_zero fun m hm => by
          by_cases h2 : 2 * m ∈ Wb
          · rw [if_pos h2, hg0 m hm, zero_mul]
          · rw [if_neg h2]
      rw [GreenCalculusOfThePrimeFreeWindow.pencilCombForm, hc0, hd0]
      ring
    have hlim0 : GreenCalculusOfThePrimeFreeWindow.pencilStepForm (-1) 3 R J σ = 0 :=
      tendsto_nhds_unique htend_pen (tendsto_const_nhds.congr' (hev0.mono fun _ h => h.symm))
    rw [hlim0, hz_sum, mul_zero] at hσ
    exact lt_irrefl 0 hσ
  have hev_lt := htend_pen.eventually
    (gt_mem_nhds (show GreenCalculusOfThePrimeFreeWindow.pencilStepForm (-1) 3 R J σ <
        -(1 / 2000) * ∑ j ∈ range J, σ j ^ 2 by linarith))
  obtain ⟨b₀, hb₀⟩ := eventually_atTop.mp hev_lt
  refine ⟨C_span, hC_span, eventually_atTop.mpr ⟨2 * R * b₀ + 3 * R + 4, fun N hN => ?_⟩⟩
  set S := Ioc N (N + 3 * K * N)
  have hQN_eq : N + 3 * K * N = (1 + 3 * K) * N := by ring
  set b := N / (2 * R) + 1
  have hb_ge1 : 1 ≤ b := by dsimp only [b]; omega
  have hb_ge_b0 : b₀ ≤ b := by
    have : b₀ ≤ N / (2 * R) :=
      (Nat.le_div_iff_mul_le (by omega : 0 < 2 * R)).mpr (by rw [mul_comm]; linarith)
    dsimp only [b]; omega
  set Wb := Ioc (R * (2 * b)) (R * (2 * b) + 2 * b * J)
  have hWb_sub : Wb ⊆ S := by
    refine Ioc_subset_Ioc ?_ ?_
    · have hgt : N < 2 * R * b := by
        dsimp only [b]; exact Nat.lt_mul_div_succ N (by omega : 0 < 2 * R)
      exact hgt.le.trans_eq (by ring)
    · have h2Rb_le : 2 * R * b ≤ N + 2 * R := by
        have h1 := Nat.mul_div_le N (2 * R)
        dsimp only [b]
        rw [mul_add, mul_one]
        exact Nat.add_le_add_right h1 (2 * R)
      have htop5000 : 5000 * (R * (2 * b) + 2 * b * J) ≤ 5000 * (4 * N) := by
        calc 5000 * (R * (2 * b) + 2 * b * J)
            = (5000 * (R + J)) * (2 * b) := by ring
          _ ≤ (10609 * R) * (2 * b) := Nat.mul_le_mul_right _ hnat5000.le
          _ = 10609 * (2 * R * b) := by ring
          _ ≤ 10609 * (N + 2 * R) := Nat.mul_le_mul_left 10609 h2Rb_le
          _ ≤ 5000 * (4 * N) := by
              have hN3R : 3 * R ≤ N := by linarith
              omega
      have htop4N : R * (2 * b) + 2 * b * J ≤ 4 * N :=
        Nat.le_of_mul_le_mul_left htop5000 (by norm_num)
      have h4N_le : 4 * N ≤ N + 3 * K * N := by
        have hKN : N ≤ K * N := Nat.le_mul_of_pos_left N hK
        calc 4 * N = N + 3 * N := by ring
          _ ≤ N + 3 * (K * N) := Nat.add_le_add_left (Nat.mul_le_mul_left 3 hKN) N
          _ = N + 3 * K * N := by ring
      exact htop4N.trans h4N_le
  let g : ℕ → ℝ := fun n => if n ∈ Wb then σ (blockIndex (R * (2 * b)) (2 * b) n) else 0
  have hmass_g : ∑ n ∈ S, g n ^ 2 = ((2 * b : ℕ) : ℝ) * ∑ j ∈ range J, σ j ^ 2 := by
    have h1 : ∑ n ∈ S, g n ^ 2 = ∑ n ∈ Wb, σ (blockIndex (R * (2 * b)) (2 * b) n) ^ 2 := by
      rw [← sum_subset hWb_sub fun n _ hn => by dsimp only [g]; rw [if_neg hn]; ring]
      exact sum_congr rfl fun n hn => by dsimp only [g]; rw [if_pos hn]
    rw [h1, sum_blockFunction_sq (R := R) (by omega : 0 < 2 * b) σ]
  have hmass_g_pos : 0 < ∑ n ∈ S, g n ^ 2 := by
    rw [hmass_g]
    exact mul_pos (by exact_mod_cast (show 0 < 2 * b by omega)) hσ_pos
  have hform_g : combFormW SelectiveArithmetic.liouvilleWeight S g <
      -(1 / 2000) * ∑ n ∈ S, g n ^ 2 := by
    have hsub_eq : combFormW SelectiveArithmetic.liouvilleWeight S g =
        combFormW SelectiveArithmetic.liouvilleWeight Wb
          (fun n => σ (blockIndex (R * (2 * b)) (2 * b) n)) :=
      (combFormW_of_subset _ hWb_sub fun n _ hn => if_neg hn).trans
        (combFormW_congr _ fun n hn => if_pos hn)
    have hlt3 : R * (2 * b) + 2 * b * J < 3 * (R * (2 * b)) := by
      calc R * (2 * b) + 2 * b * J
          = (R + J) * (2 * b) := by ring
        _ < (3 * R) * (2 * b) := Nat.mul_lt_mul_of_pos_right hJ3_lt (by omega)
        _ = 3 * (R * (2 * b)) := by ring
    rw [hsub_eq, combFormW_liouville_eq_pencilCombForm_of_lt_three hlt3, hmass_g]
    have hb_step := hb₀ b hb_ge_b0
    have h2b_pos : (0 : ℝ) < ((2 * b : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * b by omega)
    exact ((div_lt_iff₀ h2b_pos).mp hb_step).trans_eq (by ring)
  -- Represent `g` on `S = Ioc N ((1 + 3K) * N)` by centered divisibility indicators
  have hN2 : 2 ≤ N := by omega
  obtain ⟨α, hα_eq, hα_cost⟩ := hspan hN2 g
  set c := fun n => ∑ d ∈ Icc 2 ((1 + 3 * K) * N), α d * centeredMultiple d n
  have hcg_S : ∀ n ∈ S, c n = g n := fun n hn => (hα_eq n (hQN_eq ▸ hn)).symm
  have hmass_c : ∑ n ∈ S, c n ^ 2 = ∑ n ∈ S, g n ^ 2 :=
    sum_congr rfl fun n hn => by rw [hcg_S n hn]
  have hform_c : combFormW SelectiveArithmetic.liouvilleWeight S c =
      combFormW SelectiveArithmetic.liouvilleWeight S g :=
    combFormW_congr _ hcg_S
  refine ⟨α, ?_, ?_, ?_, ?_⟩
  · rw [hmass_c]; exact hmass_g_pos
  · rw [hmass_c, hQN_eq]; exact hα_cost
  · rw [hform_c, hmass_c]; exact hform_g
  · have hneg : combFormW SelectiveArithmetic.liouvilleWeight S c < 0 := by
      rw [hform_c]; linarith [hform_g, hmass_g_pos]
    rw [combFormW_eq_diagRealBudget_sub_mixedPrimeDebitW] at hneg
    linarith

/-- **Riemann Hypothesis equivalence via centered divisibility budget and debit.**
`RiemannHypothesis` holds if and only if for every comb width `K ≥ 1`, eventually in `N`,
every linear combination of centered divisibility masks on `S = Ioc N (N + 3KN)` pays
its mixed prime debit from its diagonal and real-place budget. -/
theorem riemannHypothesis_iff_centeredMultiple_debit_le_budget :
    RiemannHypothesis ↔
      ∀ K : ℕ, 1 ≤ K → ∀ᶠ N : ℕ in atTop, ∀ α : ℕ → ℝ,
        let S := Ioc N (N + 3 * K * N)
        let c := fun n => ∑ d ∈ Icc 2 ((1 + 3 * K) * N), α d * centeredMultiple d n
        mixedPrimeDebit S c ≤ diagRealBudget S c := by
  rw [riemannHypothesis_iff_eventually_combForm_nonneg]
  constructor
  · intro hRH K hK
    filter_upwards [hRH K hK] with N hN α
    rw [mixedPrimeDebit_le_diagRealBudget_iff]
    exact hN _
  · intro h K hK
    obtain ⟨C_K, _, hspan⟩ :=
      exists_centeredMultiple_comb_representation (Q := 1 + 3 * K) (by omega)
    filter_upwards [h K hK, eventually_ge_atTop 2] with N hN hN2 c
    have hQN : N + 3 * K * N = (1 + 3 * K) * N := by ring
    obtain ⟨α, hα_eq, _⟩ := hspan hN2 c
    have hdebit := (mixedPrimeDebit_le_diagRealBudget_iff _ _).mp (hN α)
    rwa [combForm_congr (fun n hn => (hα_eq n (hQN ▸ hn)).symm)] at hdebit

/-- **Sharpness of the macroscopic cost threshold for `RiemannHypothesis`.**
Even when restricted to centered-divisibility combinations satisfying the macroscopic
`ℓ^1` cost bound `(∑ |α_d|)^2 ≤ C_K N ∑_{n ∈ S} c(n)^2`, eventual payment of
`mixedPrimeDebit S c ≤ diagRealBudget S c` at every `K ≥ 1` is unconditionally
equivalent to `RiemannHypothesis`. -/
theorem riemannHypothesis_iff_macroscopic_cost_centeredMultiple_debit_le_budget :
    RiemannHypothesis ↔
      ∀ K : ℕ, 1 ≤ K → ∃ C_K : ℝ, 0 < C_K ∧
        (∀ {N : ℕ}, 2 ≤ N → ∀ c : ℕ → ℝ,
          ∃ α : ℕ → ℝ,
            (∀ n ∈ Ioc N ((1 + 3 * K) * N),
              c n = ∑ d ∈ Icc 2 ((1 + 3 * K) * N), α d * centeredMultiple d n) ∧
            (∑ d ∈ Icc 2 ((1 + 3 * K) * N), |α d|) ^ 2 ≤
              C_K * (N : ℝ) * ∑ n ∈ Ioc N ((1 + 3 * K) * N), c n ^ 2) ∧
        ∀ᶠ N : ℕ in atTop, ∀ α : ℕ → ℝ,
          let S := Ioc N (N + 3 * K * N)
          let c := fun n => ∑ d ∈ Icc 2 ((1 + 3 * K) * N), α d * centeredMultiple d n
          (∑ d ∈ Icc 2 ((1 + 3 * K) * N), |α d|) ^ 2 ≤ C_K * (N : ℝ) * ∑ n ∈ S, c n ^ 2 →
          mixedPrimeDebit S c ≤ diagRealBudget S c := by
  rw [riemannHypothesis_iff_eventually_combForm_nonneg]
  constructor
  · intro hRH K hK
    obtain ⟨C_K, hCK_pos, hspan⟩ :=
      exists_centeredMultiple_comb_representation (Q := 1 + 3 * K) (by omega)
    refine ⟨C_K, hCK_pos, hspan, ?_⟩
    filter_upwards [hRH K hK] with N hN α _
    rw [mixedPrimeDebit_le_diagRealBudget_iff]
    exact hN _
  · intro h K hK
    obtain ⟨C_K, _, hspan, hev⟩ := h K hK
    filter_upwards [hev, eventually_ge_atTop 2] with N hN hN2 c
    have hQN : N + 3 * K * N = (1 + 3 * K) * N := by ring
    obtain ⟨α, hα_eq, hα_cost⟩ := hspan hN2 c
    set S := Ioc N (N + 3 * K * N)
    set c_α := fun n => ∑ d ∈ Icc 2 ((1 + 3 * K) * N), α d * centeredMultiple d n
    have hcg : ∀ n ∈ S, c_α n = c n := fun n hn => (hα_eq n (hQN ▸ hn)).symm
    have hcost_S : (∑ d ∈ Icc 2 ((1 + 3 * K) * N), |α d|) ^ 2 ≤
        C_K * (N : ℝ) * ∑ n ∈ S, c_α n ^ 2 := by
      have hmass : ∑ n ∈ S, c_α n ^ 2 = ∑ n ∈ Ioc N ((1 + 3 * K) * N), c n ^ 2 := by
        rw [← hQN]
        exact sum_congr rfl fun n hn => by rw [hcg n hn]
      rw [hmass]
      exact hα_cost
    have hnn := (mixedPrimeDebit_le_diagRealBudget_iff _ _).mp (hN α hcost_S)
    rwa [combForm_congr hcg] at hnn

#print axioms eventually_combFormW_controlled_residue_ge
#print axioms eventually_mixedPrimeDebitW_le_diagRealBudget_of_cost
#print axioms eventually_pilot_pos_and_cauchy_schwarz
#print axioms eventually_pilot_vonMangoldt_pos_and_cauchy_schwarz
#print axioms eventually_pilot_liouville_pos_and_cauchy_schwarz
#print axioms card_primesLE_le
#print axioms eventually_combFormW_primeSpan_sqrt_ge
#print axioms sum_moebius_div_Icc_ne_zero
#print axioms exists_centeredMultiple_comb_representation
#print axioms eventually_exists_liouville_centeredMultiple_neg
#print axioms riemannHypothesis_iff_centeredMultiple_debit_le_budget
#print axioms riemannHypothesis_iff_macroscopic_cost_centeredMultiple_debit_le_budget

end GaloisForLFunctions.SignedArithmeticCorrespondences

