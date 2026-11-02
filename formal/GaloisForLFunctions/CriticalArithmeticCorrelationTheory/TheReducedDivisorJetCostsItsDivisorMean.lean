import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheNearGramFormOfAPacketCostsItsDivisorMean

/-!
# The reduced divisor jet costs its divisor mean

The near Gram operator `K₂ᵦ` (kernel `A(|log j − log n|/w)/G` on near pairs) reads only the top
rows `N ≤ 2ce² n`, and `Γ = I + K₂ᵦ` is the Gram matrix of the atoms. Hence
`‖K₂ᵦ x‖² ≤ 2ec Σ_top x² + (2ec − 1)|⟨K₂ᵦ x, x⟩|`. For a packet `x = Σ_k β_k v_k` without the
pole conductor, the top mass is `O((1 + log c)/log N) Σ β²` and the form is the divisor mean
of `exists_nearGram_packet_form_le`. Applied to the divisor jet `v_jet` minus its pole component
(`reducedDivisorJet`) and interpolated over conductor prefixes:
`‖K₂ᵦ v_jet'‖² ≤ C c ((1 + log c) Sg/log N + c⁵/N + c³R⁴/(N log N)) (1 + log R) Σ (1 + log m) a_m²`,
with `Sg ≥ σ(m)/φ(m)` on `[2, R]`.
-/

set_option autoImplicit false
noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  CriticalScaleArithmeticRigidity

/-- **The near Gram operator on the top rows.** Near pairs live on `N ≤ 2ce² n`, so
`‖K₂ᵦ x‖² ≤ 2ec Σ_{N ≤ 2ce² n} x_n² + (2ec − 1)|⟨K₂ᵦ x, x⟩|`. -/
theorem sum_nearGram_sq_le_top {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0) (hM : 0 < ∫ t, φ t ^ 2) {c : ℝ} {N : ℕ}
    (hc1 : 1 ≤ c) (hcN : c ≤ N) (hw : c / N ≤ 1) (x : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, nearGram φ c N x n ^ 2) ≤
      2 * Real.exp 1 * c *
          (∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) ≤ linearNearRowRadius c * (n : ℝ)), x n ^ 2) +
        (2 * Real.exp 1 * c - 1) * |∑ n ∈ Icc 1 N, x n * nearGram φ c N x n| := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  classical
  set y : ℕ → ℝ := fun n => if (N : ℝ) ≤ linearNearRowRadius c * n then x n else 0 with hy
  -- the operator only reads the top rows
  have hsame : ∀ n ∈ Icc 1 N, nearGram φ c N y n = nearGram φ c N x n := by
    intro n hn
    unfold nearGram
    refine sum_congr rfl fun j hj => ?_
    have := (nearRow_geometry_small_width hc0 hn hj hw).2.2
    simp only [hy, if_pos this]
  have hrow0 : ∀ n ∈ Icc 1 N, ¬((N : ℝ) ≤ linearNearRowRadius c * n) → nearGram φ c N x n = 0 := by
    intro n hn hnot
    unfold nearGram
    refine sum_eq_zero fun j hj => ?_
    exact absurd (nearRow_geometry_small_width hc0 hn hj hw).2.1 hnot
  have hform : (∑ n ∈ Icc 1 N, y n * nearGram φ c N y n) =
      ∑ n ∈ Icc 1 N, x n * nearGram φ c N x n := by
    refine sum_congr rfl fun n hn => ?_
    rw [hsame n hn]
    by_cases h : (N : ℝ) ≤ linearNearRowRadius c * n
    · simp only [hy, if_pos h]
    · simp only [hy, if_neg h, hrow0 n hn h, mul_zero]
  have hmass : (∑ n ∈ Icc 1 N, y n ^ 2) =
      ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) ≤ linearNearRowRadius c * (n : ℝ)), x n ^ 2 := by
    rw [sum_filter]
    refine sum_congr rfl fun n _ => ?_
    simp only [hy]; split_ifs <;> simp
  have hgram := sum_nearGram_sq_le_gram hφ hsupp hM hc0 hcN y
  rw [hform, hmass, sum_congr rfl fun n hn => by rw [hsame n hn]] at hgram
  set F := ∑ n ∈ Icc 1 N, x n * nearGram φ c N x n
  set T := ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) ≤ linearNearRowRadius c * (n : ℝ)), x n ^ 2
  have hT0 : 0 ≤ T := sum_nonneg fun _ _ => sq_nonneg _
  have hk : 0 ≤ 2 * Real.exp 1 * c - 1 := by
    have := Real.add_one_le_exp (1 : ℝ); nlinarith
  have hF := le_abs_self F
  nlinarith

/-- **Top mass of a packet.** On the rows `N ≤ T n` a packet of conductors `≤ Q` carries at most
`(4 + log 2K)/log N · Σ β²`, `K = ⌈T⌉ + 1`. -/
theorem sum_top_packet_sq_le {Q N : ℕ} (hQ : 2 ≤ Q) (hL : 0 < Real.log N) {T : ℝ}
    (hKN : ⌈T⌉₊ + 1 ≤ N) (hQK : Q * Q ≤ N / (⌈T⌉₊ + 1)) (β : ℕ → ℝ) :
    (∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) ≤ T * (n : ℝ)),
        primeHorizonExtension (∑ m ∈ Icc 1 Q, β m • normalizedRamanujanHorizonVector m N) n ^ 2) ≤
      (4 + Real.log (2 * ((⌈T⌉₊ + 1 : ℕ) : ℝ))) / Real.log N * ∑ m ∈ Icc 1 Q, β m ^ 2 := by
  set K := ⌈T⌉₊ + 1 with hK
  have hK1 : 1 ≤ K := by omega
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hTK : T < K := by
    have := Nat.le_ceil T
    simp only [hK]; push_cast; linarith
  have hext : ∀ n ∈ Icc 1 N,
      primeHorizonExtension (∑ m ∈ Icc 1 Q, β m • normalizedRamanujanHorizonVector m N) n ^ 2 =
        (1 / Real.log N) * (CriticalScaleArithmeticRigidity.normalizedConductorPacket Q β n ^ 2 / n) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    rw [primeHorizonExtension_coe _ ⟨n, hn⟩]
    change ((PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨n, hn⟩)
      (∑ m ∈ Icc 1 Q, β m • normalizedRamanujanHorizonVector m N)) ^ 2 = _
    rw [map_sum]
    have hterm : ∀ m ∈ Icc 1 Q, (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨n, hn⟩)
        (β m • normalizedRamanujanHorizonVector m N) =
          (Real.sqrt (Real.log N))⁻¹ * (β m * normalizedRamanujanMode m n) / Real.sqrt n := by
      intro m _
      change β m * ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m n / Real.sqrt n)) = _
      ring
    rw [sum_congr rfl hterm, ← sum_div, ← mul_sum, div_pow, mul_pow, inv_pow,
      Real.sq_sqrt hL.le, Real.sq_sqrt hn0.le]
    unfold CriticalScaleArithmeticRigidity.normalizedConductorPacket
    ring
  have hsub : (Icc 1 N).filter (fun n : ℕ => (N : ℝ) ≤ T * (n : ℝ)) ⊆ Ioc (N / K) N := by
    intro n hn
    obtain ⟨hnI, hTn⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hnI
    refine mem_Ioc.mpr ⟨?_, hnN⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hlt : (N : ℝ) < K * n := lt_of_le_of_lt hTn (by nlinarith)
    have : N < K * n := by exact_mod_cast hlt
    exact (Nat.div_lt_iff_lt_mul hK1).mpr (by linarith)
  calc _ = ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) ≤ T * (n : ℝ)),
        (1 / Real.log N) * (CriticalScaleArithmeticRigidity.normalizedConductorPacket Q β n ^ 2 / n) :=
        sum_congr rfl fun n hn => hext n (mem_filter.mp hn).1
    _ ≤ ∑ n ∈ Ioc (N / K) N,
        (1 / Real.log N) * (CriticalScaleArithmeticRigidity.normalizedConductorPacket Q β n ^ 2 / n) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = (1 / Real.log N) * ∑ n ∈ Ioc (N / K) N,
        CriticalScaleArithmeticRigidity.normalizedConductorPacket Q β n ^ 2 / n := (mul_sum ..).symm
    _ ≤ (1 / Real.log N) * (terminalPacketCost Q (N / K) N * ∑ m ∈ Icc 1 Q, β m ^ 2) :=
        mul_le_mul_of_nonneg_left (CriticalScaleArithmeticRigidity.harmonicConductorPacket_terminal_le
          hQ (Nat.div_le_self N K) β) (by positivity)
    _ ≤ (1 / Real.log N) * ((4 + Real.log (2 * (K : ℝ))) * ∑ m ∈ Icc 1 Q, β m ^ 2) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (CriticalScaleArithmeticRigidity.terminalPacketCost_nat_div_le hK1 hKN hQK)
          (sum_nonneg fun _ _ => sq_nonneg _)) (by positivity)
    _ = _ := by ring

/-- **The near Gram operator on a packet without the pole conductor.** For
`x = Σ_{k ≤ M} β_k v_k` with `β 1 = 0`, `‖K₂ᵦ x‖² ≤ 2ec ((4 + log 2K)/log N Σβ² +
C (c⁵/N + (1 + log c) Sg/log N + c³M⁴/(N log N)) ‖x‖²)`, `K = ⌈2ce²⌉ + 1`. -/
theorem exists_nearGram_reducedPacket_sq_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0) (hM : 0 < ∫ t, φ t ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M N : ℕ} {c : ℝ}, 2 ≤ M → M * M ≤ N →
      18 * (1 + Real.log M) ≤ Real.log N → 1 ≤ c → c / N ≤ 1 →
      4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ⌈linearNearRowRadius c⌉₊ + 1 ≤ N → M * M ≤ N / (⌈linearNearRowRadius c⌉₊ + 1) →
      ∀ {β : ℕ → ℝ}, β 1 = 0 → ∀ {Sg : ℝ},
        (∀ m ∈ Icc 2 M, (ArithmeticFunction.sigma 1 m : ℝ) / m.totient ≤ Sg) →
        (∑ n ∈ Icc 1 N, nearGram φ c N (primeHorizonExtension
            (∑ k ∈ Icc 1 M, β k • normalizedRamanujanHorizonVector k N)) n ^ 2) ≤
          2 * Real.exp 1 * c *
            ((4 + Real.log (2 * ((⌈linearNearRowRadius c⌉₊ + 1 : ℕ) : ℝ))) / Real.log N *
                ∑ k ∈ Icc 1 M, β k ^ 2 +
              C * (c ^ 5 / N + (1 + Real.log c) * Sg / Real.log N +
                c ^ 3 * (M : ℝ) ^ 4 / (N * Real.log N)) *
                ‖∑ k ∈ Icc 1 M, β k • normalizedRamanujanHorizonVector k N‖ ^ 2) := by
  obtain ⟨C_F, hCF, hform⟩ := exists_nearGram_packet_form_le hφ hsupp hM
  refine ⟨C_F, hCF, ?_⟩
  intro M N c hM2 hMN hlog hc1 hw hradN hKN hMK β hβ1 Sg hSg
  set x := ∑ k ∈ Icc 1 M, β k • normalizedRamanujanHorizonVector k N with hx
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log N := by have := Real.log_natCast_nonneg M; linarith
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := le_trans (by omega) hKN
    exact_mod_cast this
  have hcN : c ≤ N := by
    have := (div_le_one (by linarith : (0 : ℝ) < N)).mp hw; exact this
  have htop := sum_nearGram_sq_le_top hφ hsupp hM hc1 hcN hw (primeHorizonExtension x)
  have hmass := sum_top_packet_sq_le hM2 hL0 hKN hMK β
  rw [← hx] at hmass
  have hF := hform hM2 hMN hlog hc1 hw hradN hβ1 hSg
  rw [← hx] at hF
  have he : 0 ≤ 2 * Real.exp 1 * c := by positivity
  have hk : 0 ≤ 2 * Real.exp 1 * c - 1 := by
    have := Real.add_one_le_exp (1 : ℝ); nlinarith
  set F := |∑ n ∈ Icc 1 N, primeHorizonExtension x n * nearGram φ c N (primeHorizonExtension x) n|
  set B := C_F * (c ^ 5 / N + (1 + Real.log c) * Sg / Real.log N +
    c ^ 3 * (M : ℝ) ^ 4 / (N * Real.log N)) * ‖x‖ ^ 2
  have hF0 : 0 ≤ F := abs_nonneg _
  have h1 : (2 * Real.exp 1 * c - 1) * F ≤ 2 * Real.exp 1 * c * B := by
    have := mul_le_mul_of_nonneg_left hF hk
    have h2 : (2 * Real.exp 1 * c - 1) * B ≤ 2 * Real.exp 1 * c * B := by
      have hB0 : 0 ≤ B := le_trans hF0 hF
      nlinarith
    linarith
  have h2 := mul_le_mul_of_nonneg_left hmass he
  nlinarith

/-! ### The divisor jet without its pole conductor -/

/-- The divisor jet with its pole conductor `k = 1` removed. -/
def reducedDivisorJet (M N : ℕ) (a : ℕ → ℝ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  ∑ k ∈ Icc 1 M, (if k = 1 then 0 else divisorJetCoeff M a k) • normalizedRamanujanHorizonVector k N

theorem divisorJetHorizonVector_eq_reduced_add {M : ℕ} (hM : 1 ≤ M) (N : ℕ) (a : ℕ → ℝ) :
    divisorJetHorizonVector M N a =
      reducedDivisorJet M N a + divisorJetCoeff M a 1 • normalizedRamanujanHorizonVector 1 N := by
  unfold divisorJetHorizonVector reducedDivisorJet
  have h1 : (1 : ℕ) ∈ Icc 1 M := mem_Icc.mpr ⟨le_rfl, hM⟩
  rw [← add_sum_erase _ _ h1, ← add_sum_erase _ _ h1, if_pos rfl, zero_smul, zero_add, add_comm]
  congr 1
  exact sum_congr rfl fun k hk => by rw [if_neg (ne_of_mem_erase hk)]

theorem divisorJetCoeff_add (M : ℕ) (a b : ℕ → ℝ) (k : ℕ) :
    divisorJetCoeff M (a + b) k = divisorJetCoeff M a k + divisorJetCoeff M b k := by
  unfold divisorJetCoeff
  rw [← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  split_ifs
  · simp only [Pi.add_apply]; ring
  · ring

theorem divisorJetCoeff_smul (M : ℕ) (s : ℝ) (a : ℕ → ℝ) (k : ℕ) :
    divisorJetCoeff M (s • a) k = s * divisorJetCoeff M a k := by
  unfold divisorJetCoeff
  rw [mul_sum]
  refine sum_congr rfl fun m _ => ?_
  split_ifs
  · simp only [Pi.smul_apply, smul_eq_mul]; ring
  · ring

theorem divisorJetCoeff_congr {M : ℕ} {a b : ℕ → ℝ} (hab : ∀ m ∈ Icc 1 M, a m = b m) (k : ℕ) :
    divisorJetCoeff M a k = divisorJetCoeff M b k := by
  unfold divisorJetCoeff
  exact sum_congr rfl fun m hm => by rw [hab m hm]

theorem reducedDivisorJet_add (M N : ℕ) (a b : ℕ → ℝ) :
    reducedDivisorJet M N (a + b) = reducedDivisorJet M N a + reducedDivisorJet M N b := by
  unfold reducedDivisorJet
  rw [← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [← add_smul]
  congr 1
  split_ifs
  · ring
  · exact divisorJetCoeff_add M a b k

theorem reducedDivisorJet_smul (M N : ℕ) (s : ℝ) (a : ℕ → ℝ) :
    reducedDivisorJet M N (s • a) = s • reducedDivisorJet M N a := by
  unfold reducedDivisorJet
  rw [smul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [smul_smul]
  congr 1
  split_ifs
  · ring
  · exact divisorJetCoeff_smul M s a k

theorem reducedDivisorJet_congr {M N : ℕ} {a b : ℕ → ℝ} (hab : ∀ m ∈ Icc 1 M, a m = b m) :
    reducedDivisorJet M N a = reducedDivisorJet M N b := by
  unfold reducedDivisorJet
  exact sum_congr rfl fun k _ => by rw [divisorJetCoeff_congr hab k]

theorem divisorJetCoeff_eq_zero_of_lt {M : ℕ} (a : ℕ → ℝ) {k : ℕ} (hk : M < k) :
    divisorJetCoeff M a k = 0 := by
  unfold divisorJetCoeff
  refine sum_eq_zero fun m hm => ?_
  rw [if_neg]
  intro hkm
  have h1 := Nat.divisor_le hkm
  have h2 := (mem_Icc.mp hm).2
  omega

/-- A packet supported on `[1, M]` has the same reduced jet at every larger prefix. -/
theorem reducedDivisorJet_eq_of_support {M R N : ℕ} (hMR : M ≤ R) {a : ℕ → ℝ}
    (ha : ∀ m ∈ Icc 1 R, M < m → a m = 0) :
    reducedDivisorJet R N a = reducedDivisorJet M N a := by
  have hcoeff : ∀ k, divisorJetCoeff R a k = divisorJetCoeff M a k := by
    intro k
    unfold divisorJetCoeff
    symm
    apply sum_subset (Icc_subset_Icc le_rfl hMR)
    intro m hm hmM
    have hlt : M < m := by
      by_contra h
      exact hmM (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, not_lt.mp h⟩)
    rw [ha m hm hlt]
    split_ifs <;> simp
  unfold reducedDivisorJet
  simp only [hcoeff]
  symm
  apply sum_subset (Icc_subset_Icc le_rfl hMR)
  intro k hk hkM
  have hlt : M < k := by
    by_contra h
    exact hkM (mem_Icc.mpr ⟨(mem_Icc.mp hk).1, not_lt.mp h⟩)
  rw [divisorJetCoeff_eq_zero_of_lt a hlt]
  split_ifs <;> simp

/-- The reduced jet coefficients cost `O((1 + log M)²)` per unit band mass. -/
theorem exists_reducedDivisorJet_coeff_sq_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M N : ℕ}, 2 ≤ M → M * M ≤ N → 18 * (1 + Real.log M) ≤ Real.log N →
      ∀ a : ℕ → ℝ,
        (∑ k ∈ Icc 1 M, (if k = 1 then 0 else divisorJetCoeff M a k) ^ 2) ≤
          C * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
  obtain ⟨C_jet, _, hjet⟩ := exists_divisorJetHorizonVector_norm_le
  refine ⟨2 * C_jet ^ 2, by positivity, ?_⟩
  intro M N hM hMN hlog a
  have hR := (half_and_three_halves_riesz_of_log_le hM hMN hlog (divisorJetCoeff M a)).1
  have hj := pow_le_pow_left₀ (norm_nonneg _) (hjet hM hMN hlog a) 2
  rw [mul_pow, mul_pow, Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)] at hj
  have hle : (∑ k ∈ Icc 1 M, (if k = 1 then 0 else divisorJetCoeff M a k) ^ 2) ≤
      ∑ k ∈ Icc 1 M, divisorJetCoeff M a k ^ 2 :=
    sum_le_sum fun k _ => by split_ifs <;> nlinarith [sq_nonneg (divisorJetCoeff M a k)]
  have hdef : divisorJetHorizonVector M N a =
      ∑ k ∈ Icc 1 M, divisorJetCoeff M a k • normalizedRamanujanHorizonVector k N := rfl
  rw [← hdef] at hR
  linarith

theorem norm_nearDivisorJetKernel_sq_eq (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ‖Matrix.toEuclideanLin (nearDivisorJetKernelMatrix φ c N) v‖ ^ 2 =
      ∑ n ∈ Icc 1 N, nearGram φ c N (primeHorizonExtension v) n ^ 2 := by
  rw [← sum_primeHorizonExtension_sq]
  exact sum_congr rfl fun n hn => by rw [nearDivisorJetKernelMatrix_row φ c N v n hn]; rfl

/-- `4 + log 2K ≤ 13 (1 + log c)` for `K = ⌈2ce²⌉ + 1`. -/
theorem four_add_log_two_nearCeil_le {c : ℝ} (hc1 : 1 ≤ c) :
    4 + Real.log (2 * ((⌈linearNearRowRadius c⌉₊ + 1 : ℕ) : ℝ)) ≤ 13 * (1 + Real.log c) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have he2 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  have hr0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
  have hceil := Nat.ceil_lt_add_one hr0
  have hK : (2 * ((⌈linearNearRowRadius c⌉₊ + 1 : ℕ) : ℝ)) ≤ 8 * c * Real.exp 2 := by
    push_cast
    unfold linearNearRowRadius at hceil ⊢
    nlinarith
  have hK0 : 0 < 2 * ((⌈linearNearRowRadius c⌉₊ + 1 : ℕ) : ℝ) := by positivity
  have hlog := Real.log_le_log hK0 hK
  have hRl : Real.log (8 * c * Real.exp 2) = Real.log 8 + Real.log c + 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hc0.ne',
      Real.log_exp]
  rw [hRl] at hlog
  have h8 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
  have hlc := Real.log_nonneg hc1
  linarith

/-- **`K₂ᵦ` on a reduced divisor jet, one prefix.** For a band `b` of conductors `≤ M`,
`‖K₂ᵦ v_jet'‖² ≤ C c ((1 + log c) Sg/log N + c⁵/N + c³M⁴/(N log N)) (1 + log M)² Σ b²`. -/
theorem exists_nearGram_reducedDivisorJet_sq_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0) (hM : 0 < ∫ t, φ t ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M N : ℕ} {c : ℝ}, 2 ≤ M → M * M ≤ N →
      18 * (1 + Real.log M) ≤ Real.log N → 1 ≤ c → c / N ≤ 1 →
      4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ⌈linearNearRowRadius c⌉₊ + 1 ≤ N → M * M ≤ N / (⌈linearNearRowRadius c⌉₊ + 1) →
      ∀ {Sg : ℝ}, 1 ≤ Sg →
        (∀ m ∈ Icc 2 M, (ArithmeticFunction.sigma 1 m : ℝ) / m.totient ≤ Sg) → ∀ b : ℕ → ℝ,
        ‖Matrix.toEuclideanLin (nearDivisorJetKernelMatrix φ c N) (reducedDivisorJet M N b)‖ ^ 2 ≤
          C * c * ((1 + Real.log c) * Sg / Real.log N + c ^ 5 / N +
              c ^ 3 * (M : ℝ) ^ 4 / (N * Real.log N)) *
            (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, b m ^ 2 := by
  obtain ⟨C_F, hCF, hop⟩ := exists_nearGram_reducedPacket_sq_le hφ hsupp hM
  obtain ⟨C_r, hCr, hcoef⟩ := exists_reducedDivisorJet_coeff_sq_le
  refine ⟨2 * Real.exp 1 * (13 + 3 / 2 * C_F) * C_r, by positivity, ?_⟩
  intro M N c hM2 hMN hlog hc1 hw hradN hKN hMK Sg hSg1 hSg b
  set β : ℕ → ℝ := fun k => if k = 1 then 0 else divisorJetCoeff M b k with hβ
  have hβ1 : β 1 = 0 := by simp only [hβ, if_pos rfl]
  have hx : reducedDivisorJet M N b = ∑ k ∈ Icc 1 M, β k • normalizedRamanujanHorizonVector k N :=
    rfl
  rw [norm_nearDivisorJetKernel_sq_eq, hx]
  have h1 := hop hM2 hMN hlog hc1 hw hradN hKN hMK hβ1 hSg
  have hRz := (half_and_three_halves_riesz_of_log_le hM2 hMN hlog β).2
  have hcf := hcoef hM2 hMN hlog b
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log N := by have := Real.log_natCast_nonneg M; linarith
  have hA := four_add_log_two_nearCeil_le hc1
  set D := (1 + Real.log c) * Sg / Real.log N + c ^ 5 / N + c ^ 3 * (M : ℝ) ^ 4 / (N * Real.log N)
    with hD
  set B := ∑ k ∈ Icc 1 M, β k ^ 2 with hB
  set X := ‖∑ k ∈ Icc 1 M, β k • normalizedRamanujanHorizonVector k N‖ ^ 2
  have hlc := Real.log_nonneg hc1
  have hD0 : 0 ≤ D := by positivity
  have hB0 : 0 ≤ B := sum_nonneg fun _ _ => sq_nonneg _
  have hAD : (4 + Real.log (2 * ((⌈linearNearRowRadius c⌉₊ + 1 : ℕ) : ℝ))) / Real.log N ≤
      13 * D := by
    rw [div_le_iff₀ hL0]
    have : (1 + Real.log c) * Sg / Real.log N * Real.log N = (1 + Real.log c) * Sg := by
      field_simp
    have h2 : 0 ≤ (c ^ 5 / N + c ^ 3 * (M : ℝ) ^ 4 / (N * Real.log N)) * Real.log N := by
      positivity
    have h3 : 13 * (1 + Real.log c) ≤ 13 * ((1 + Real.log c) * Sg) := by nlinarith
    calc _ ≤ 13 * (1 + Real.log c) := hA
      _ ≤ 13 * ((1 + Real.log c) * Sg) := h3
      _ ≤ 13 * D * Real.log N := by rw [hD]; nlinarith
  have hD' : c ^ 5 / N + (1 + Real.log c) * Sg / Real.log N +
      c ^ 3 * (M : ℝ) ^ 4 / (N * Real.log N) = D := by rw [hD]; ring
  rw [hD'] at h1
  have hinner : (4 + Real.log (2 * ((⌈linearNearRowRadius c⌉₊ + 1 : ℕ) : ℝ))) / Real.log N * B +
      C_F * D * X ≤ (13 + 3 / 2 * C_F) * D * B := by
    have e1 := mul_le_mul_of_nonneg_right hAD hB0
    have e2 := mul_le_mul_of_nonneg_left hRz (mul_nonneg hCF hD0)
    nlinarith
  have he : 0 ≤ 2 * Real.exp 1 * c := by positivity
  have hstep := h1.trans (mul_le_mul_of_nonneg_left hinner he)
  have hfin : (13 + 3 / 2 * C_F) * D * B ≤
      (13 + 3 / 2 * C_F) * D * (C_r * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, b m ^ 2) :=
    mul_le_mul_of_nonneg_left hcf (by positivity)
  calc _ ≤ 2 * Real.exp 1 * c * ((13 + 3 / 2 * C_F) * D * B) := hstep
    _ ≤ 2 * Real.exp 1 * c * ((13 + 3 / 2 * C_F) * D *
          (C_r * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, b m ^ 2)) :=
        mul_le_mul_of_nonneg_left hfin he
    _ = _ := by ring

/-- **`K₂ᵦ` on the reduced divisor jet of a band.** Interpolating the prefix bounds over
conductor prefixes, for `a` on `[1, R]`:
`‖K₂ᵦ v_jet'‖² ≤ C c ((1 + log c) Sg/log N + c⁵/N + c³R⁴/(N log N)) (1 + log R) Σ (1 + log m) a_m²`. -/
theorem exists_nearGram_reducedDivisorJet_sq_le_weighted {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0) (hM : 0 < ∫ t, φ t ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R N : ℕ} {c : ℝ}, 2 ≤ R →
      18 * (1 + Real.log R) ≤ Real.log N → 1 ≤ c → c / N ≤ 1 →
      4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ⌈linearNearRowRadius c⌉₊ + 1 ≤ N → R * R ≤ N / (⌈linearNearRowRadius c⌉₊ + 1) →
      ∀ {Sg : ℝ}, 1 ≤ Sg →
        (∀ m ∈ Icc 2 R, (ArithmeticFunction.sigma 1 m : ℝ) / m.totient ≤ Sg) → ∀ a : ℕ → ℝ,
        ‖Matrix.toEuclideanLin (nearDivisorJetKernelMatrix φ c N) (reducedDivisorJet R N a)‖ ^ 2 ≤
          C * c * ((1 + Real.log c) * Sg / Real.log N + c ^ 5 / N +
              c ^ 3 * (R : ℝ) ^ 4 / (N * Real.log N)) *
            (1 + Real.log R) * ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2 := by
  obtain ⟨C_1, hC1, hpre⟩ := exists_nearGram_reducedDivisorJet_sq_le hφ hsupp hM
  refine ⟨32 * C_1, by positivity, ?_⟩
  intro R N c hR hlog hc1 hw hradN hKN hRK Sg hSg1 hSg a
  classical
  set A := Matrix.toEuclideanLin (nearDivisorJetKernelMatrix φ c N) with hA
  have hRN : R * R ≤ N := hRK.trans (Nat.div_le_self _ _)
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log N := by have := Real.log_natCast_nonneg R; linarith
  set D := (1 + Real.log c) * Sg / Real.log N + c ^ 5 / N + c ^ 3 * (R : ℝ) ^ 4 / (N * Real.log N)
    with hD
  have hD0 : 0 ≤ D := by have := Real.log_nonneg hc1; positivity
  let ext : (↥(Icc 1 R) → ℝ) → ℕ → ℝ := fun b m => if hm : m ∈ Icc 1 R then b ⟨m, hm⟩ else 0
  have hext_add : ∀ b d, ext (b + d) = ext b + ext d := by
    intro b d; funext m; simp only [ext, Pi.add_apply]; split_ifs <;> simp
  have hext_smul : ∀ (s : ℝ) b, ext (s • b) = s • ext b := by
    intro s b; funext m; simp only [ext, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp
  let f : (↥(Icc 1 R) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (PrimeHorizonIndex N) :=
    { toFun := fun b => A (reducedDivisorJet R N (ext b))
      map_add' := by intro b d; simp only [hext_add, reducedDivisorJet_add, map_add]
      map_smul' := by
        intro s b; simp only [hext_smul, reducedDivisorJet_smul, map_smul, RingHom.id_apply] }
  let w_log : ↥(Icc 1 R) → ℝ := fun i => 1 + Real.log (i : ℕ)
  have hw_log : ∀ i, 1 ≤ w_log i := fun i => by
    dsimp only [w_log]; linarith [Real.log_natCast_nonneg (i : ℕ)]
  set C_0 := Real.sqrt (4 * C_1 * c * D) with hC0
  have hC0_sq : C_0 ^ 2 = 4 * C_1 * c * D := Real.sq_sqrt (by positivity)
  have hprefix : ∀ t : ℝ, 1 ≤ t → ∀ b : ↥(Icc 1 R) → ℝ, (∀ i, t < w_log i → b i = 0) →
      ‖f b‖ ^ 2 ≤ C_0 ^ 2 * t ^ 2 * ∑ i, b i ^ 2 := by
    intro t ht b hb
    have hb' (m : ℕ) (hm : m ∈ Icc 1 R) : ext b m = b ⟨m, hm⟩ := dif_pos hm
    have hmass : (∑ m ∈ Icc 1 R, ext b m ^ 2) = ∑ i, b i ^ 2 := by
      rw [← sum_coe_sort (Icc 1 R) (fun m => ext b m ^ 2)]
      exact sum_congr rfl fun i _ => by rw [hb' i i.property]
    let Sb := (Icc 1 R).filter (fun m => ext b m ≠ 0)
    by_cases hS : Sb.Nonempty
    · let M := max 2 (Sb.max' hS)
      have hM2 : 2 ≤ M := le_max_left _ _
      have htop : Sb.max' hS ∈ Icc 1 R := (mem_filter.mp (Sb.max'_mem hS)).1
      have hMR : M ≤ R := max_le hR (mem_Icc.mp htop).2
      have hzero (m : ℕ) (hm : m ∈ Icc 1 R) (hmM : M < m) : ext b m = 0 := by
        by_contra hz
        have hs : m ∈ Sb := mem_filter.mpr ⟨hm, hz⟩
        have hle : m ≤ M := (Finset.le_max' Sb m hs).trans (le_max_right _ _)
        omega
      have hjet_eq := reducedDivisorJet_eq_of_support (N := N) hMR hzero
      have hHM : 1 + Real.log M ≤ 2 * t := by
        by_cases htop2 : Sb.max' hS ≤ 2
        · have hMeq : M = 2 := max_eq_left htop2
          rw [hMeq]
          have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          simp only [Nat.cast_ofNat]
          linarith only [hl, ht]
        · have hMeq : M = Sb.max' hS := max_eq_right (le_of_not_ge htop2)
          have hbound : 1 + Real.log (Sb.max' hS) ≤ t := by
            by_contra h
            have hz := hb ⟨Sb.max' hS, htop⟩ (lt_of_not_ge h)
            have hnz := (mem_filter.mp (Sb.max'_mem hS)).2
            rw [hb' (Sb.max' hS) htop, hz] at hnz
            exact hnz rfl
          rw [hMeq]
          linarith only [hbound, ht]
      have hMM : M * M ≤ N := (Nat.mul_le_mul hMR hMR).trans hRN
      have hlM : Real.log M ≤ Real.log R := Real.log_le_log
        (by exact_mod_cast (show 0 < M by omega)) (by exact_mod_cast hMR)
      have hlogM : 18 * (1 + Real.log M) ≤ Real.log N := by linarith only [hlM, hlog]
      have hMK : M * M ≤ N / (⌈linearNearRowRadius c⌉₊ + 1) :=
        (Nat.mul_le_mul hMR hMR).trans hRK
      have hSgM : ∀ m ∈ Icc 2 M, (ArithmeticFunction.sigma 1 m : ℝ) / m.totient ≤ Sg :=
        fun m hm => hSg m (Icc_subset_Icc le_rfl hMR hm)
      have hb_pre := hpre hM2 hMM hlogM hc1 hw hradN hKN hMK hSg1 hSgM (ext b)
      have hm_sub : (∑ m ∈ Icc 1 M, ext b m ^ 2) ≤ ∑ i, b i ^ 2 := by
        rw [← hmass]
        exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hMR) fun _ _ _ => sq_nonneg _
      have hDM : (1 + Real.log c) * Sg / Real.log N + c ^ 5 / N +
          c ^ 3 * (M : ℝ) ^ 4 / (N * Real.log N) ≤ D := by
        rw [hD]
        have hM4 : (M : ℝ) ^ 4 ≤ (R : ℝ) ^ 4 :=
          pow_le_pow_left₀ (by positivity) (by exact_mod_cast hMR) 4
        have : c ^ 3 * (M : ℝ) ^ 4 / (N * Real.log N) ≤ c ^ 3 * (R : ℝ) ^ 4 / (N * Real.log N) := by
          gcongr
        linarith
      have hsq : (1 + Real.log M) ^ 2 ≤ (2 * t) ^ 2 :=
        pow_le_pow_left₀ (by have := Real.log_natCast_nonneg M; linarith) hHM 2
      change ‖A (reducedDivisorJet R N (ext b))‖ ^ 2 ≤ _
      rw [hjet_eq]
      have hnn : 0 ≤ C_1 * c := by positivity
      calc _ ≤ C_1 * c * ((1 + Real.log c) * Sg / Real.log N + c ^ 5 / N +
              c ^ 3 * (M : ℝ) ^ 4 / (N * Real.log N)) * (1 + Real.log M) ^ 2 *
              ∑ m ∈ Icc 1 M, ext b m ^ 2 := hb_pre
        _ ≤ C_1 * c * D * (2 * t) ^ 2 * ∑ i, b i ^ 2 := by
          gcongr
        _ = C_0 ^ 2 * t ^ 2 * ∑ i, b i ^ 2 := by rw [hC0_sq]; ring
    · have hb0 : ∀ i, b i = 0 := by
        intro i
        by_contra hi
        apply hS
        exact ⟨i, mem_filter.mpr ⟨i.property, by rwa [hb' i i.property]⟩⟩
      rw [show b = 0 from funext hb0, _root_.map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      positivity
  have hH1 : 1 ≤ 1 + Real.log R := by linarith only [Real.log_natCast_nonneg R]
  have hmax : ∀ i, w_log i ≤ 1 + Real.log R := fun i => by
    have hi0 : (0 : ℝ) < (i : ℕ) := by exact_mod_cast (mem_Icc.mp i.property).1
    have hiR : ((i : ℕ) : ℝ) ≤ R := by exact_mod_cast (mem_Icc.mp i.property).2
    dsimp only [w_log]
    linarith only [Real.log_le_log hi0 hiR]
  have hinterp := linear_packet_sq_le_weighted_of_prefix_bound f w_log hw_log C_0
    hprefix hH1 hmax (fun i => a i)
  have hf_apply : f (fun i => a i) = A (reducedDivisorJet R N a) := by
    change A (reducedDivisorJet R N (ext fun i => a i)) = _
    congr 1
    exact reducedDivisorJet_congr fun m hm => dif_pos hm
  have henergy : (∑ i : ↥(Icc 1 R), w_log i * a i ^ 2) =
      ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2 :=
    sum_coe_sort (Icc 1 R) (fun m => (1 + Real.log m) * a m ^ 2)
  rw [hf_apply, henergy, hC0_sq] at hinterp
  refine hinterp.trans_eq ?_
  ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
