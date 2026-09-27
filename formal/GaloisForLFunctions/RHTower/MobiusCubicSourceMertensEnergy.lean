import GaloisForLFunctions.RHTower.MobiusAbelPrefixGramIntegral
import GaloisForLFunctions.RHTower.DeningerMertensSummatory
import GaloisForLFunctions.RHTower.GaussSpikeMass

/-!
# The unconditional Mertens saving for the finite cubic Möbius source

With `E(x) = exp(-(log x)^{1/3}/108)` the corpus proves `|M(n)| ≤ B n E(n)` for all large `n`.
The saving factor is slowly varying: `E(n) ≤ K_η E(N) (N/n)^η` for `1 ≤ n ≤ N` and every `η > 0`,
because the cube root is subadditive.  Summation by parts of the literal cubic source
`S_N = M(N) f_N + Σ_{n<N} M(n)(f_n - f_(n+1))` and the Gamma-norm Lipschitz law then give, for
every `0 ≤ δ < 1`,

`‖S_N‖_δ ≤ C_δ N^((1-δ)/2) E(N)`   for all large `N`.
-/

open Filter Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHTower.CubicGamma

/-- The saving factor `E(x) = exp(-(log x)^{1/3}/108)`. -/
abbrev mertensSaving (x : ℝ) : ℝ := deningerMertensSaving x

theorem mertensSaving_pos (x : ℝ) : 0 < mertensSaving x := deningerMertensSaving_pos x

/-- `u^{1/3}/108 ≤ K + η u` for `u ≥ 0`. -/
theorem cubeRoot_div_le_linear {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ u : ℝ, 0 ≤ u → u ^ ((1 : ℝ) / 3) / 108 ≤ K + η * u := by
  set U : ℝ := (108 * η) ^ (-(3 : ℝ) / 2) with hU
  have hU0 : 0 < U := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨U ^ ((1 : ℝ) / 3) / 108, fun u hu => ?_⟩
  rcases le_or_gt u U with h | h
  · have : u ^ ((1 : ℝ) / 3) ≤ U ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow hu h (by norm_num)
    have : 0 ≤ η * u := by positivity
    linarith
  · -- for `u ≥ U`, `u^{1/3} ≤ 108 η u`
    have hu0 : 0 < u := hU0.trans h
    have key : u ^ ((1 : ℝ) / 3) ≤ 108 * η * u := by
      have h23 : U ^ ((2 : ℝ) / 3) = (108 * η)⁻¹ := by
        rw [hU, ← Real.rpow_mul (by positivity)]
        rw [show -(3 : ℝ) / 2 * (2 / 3) = -1 by norm_num, Real.rpow_neg_one]
      have hmono : U ^ ((2 : ℝ) / 3) ≤ u ^ ((2 : ℝ) / 3) :=
        Real.rpow_le_rpow hU0.le h.le (by norm_num)
      have hsplit : u = u ^ ((1 : ℝ) / 3) * u ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_add hu0]; norm_num
      have hp : 0 < u ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hu0 _
      calc u ^ ((1 : ℝ) / 3) = u ^ ((1 : ℝ) / 3) * ((108 * η) * (108 * η)⁻¹) := by
            field_simp
        _ ≤ u ^ ((1 : ℝ) / 3) * ((108 * η) * u ^ ((2 : ℝ) / 3)) := by
            rw [← h23]; gcongr
        _ = 108 * η * (u ^ ((1 : ℝ) / 3) * u ^ ((2 : ℝ) / 3)) := by ring
        _ = 108 * η * u := by rw [← hsplit]
    have hK : 0 ≤ U ^ ((1 : ℝ) / 3) / 108 := by positivity
    linarith

/-- **Slow variation of the saving.**  For `η > 0` there is `K` with
`E(n) ≤ K E(N) (N/n)^η` whenever `1 ≤ n ≤ N`. -/
theorem mertensSaving_slow {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ n N : ℝ, 1 ≤ n → n ≤ N →
      mertensSaving n ≤ K * mertensSaving N * (N / n) ^ η := by
  obtain ⟨K, hK⟩ := cubeRoot_div_le_linear hη
  refine ⟨Real.exp K, Real.exp_pos _, fun n N hn hnN => ?_⟩
  have hN : 1 ≤ N := hn.trans hnN
  have ln0 : 0 ≤ Real.log n := Real.log_nonneg hn
  have lN : Real.log n ≤ Real.log N := Real.log_le_log (by linarith) hnN
  have hsub : Real.log N ^ ((1 : ℝ) / 3) ≤
      Real.log n ^ ((1 : ℝ) / 3) + (Real.log N - Real.log n) ^ ((1 : ℝ) / 3) := by
    have := Real.rpow_add_le_add_rpow ln0 (by linarith : 0 ≤ Real.log N - Real.log n)
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 : ℝ) / 3 ≤ 1)
    simpa using this
  have hlin := hK (Real.log N - Real.log n) (by linarith)
  have hratio : (N / n) ^ η = Real.exp (η * (Real.log N - Real.log n)) := by
    rw [Real.rpow_def_of_pos (div_pos (by linarith) (by linarith)),
      Real.log_div (by linarith) (by linarith)]
    ring_nf
  unfold mertensSaving deningerMertensSaving
  rw [hratio, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- `E(N) ≥ K⁻¹ N^(-η)`: the saving is sub-polynomial. -/
theorem mertensSaving_ge {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℝ, 1 ≤ N → K⁻¹ * N ^ (-η) ≤ mertensSaving N := by
  obtain ⟨K, hK, h⟩ := mertensSaving_slow hη
  refine ⟨K, hK, fun N hN => ?_⟩
  have h1 := h 1 N le_rfl hN
  have hE1 : mertensSaving 1 = 1 := by
    simp [mertensSaving, deningerMertensSaving]
  rw [hE1, div_one] at h1
  have hNpos : 0 < N ^ η := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.rpow_neg (by linarith)]
  have : K⁻¹ * (N ^ η)⁻¹ * (K * N ^ η) = 1 := by field_simp
  have hE := mertensSaving_pos N
  nlinarith [mul_pos (inv_pos.mpr hK) (inv_pos.mpr hNpos)]

/-- `Σ_{n ≤ N} n^(-s) E(n) ≤ C N^(1-s) E(N)` for `0 < s < 1`. -/
theorem sum_rpow_neg_mul_mertensSaving_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-s) * mertensSaving n ≤
        C * (N : ℝ) ^ (1 - s) * mertensSaving N := by
  set η := (1 - s) / 2 with hη_def
  have hη : 0 < η := by rw [hη_def]; linarith
  obtain ⟨K, hK, hslow⟩ := mertensSaving_slow hη
  obtain ⟨K', hK', hge⟩ := mertensSaving_ge hη
  have hc0 : 0 < s + η := by linarith
  have hc1 : s + η < 1 := by rw [hη_def]; linarith
  refine ⟨K * (1 / (1 - (s + η)) + K'), by positivity, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hterm : ∀ n ∈ Icc 1 N, (n : ℝ) ^ (-s) * mertensSaving n ≤
      K * mertensSaving N * (N : ℝ) ^ η * (n : ℝ) ^ (-(s + η)) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    have hnpos : (0 : ℝ) < n := by linarith
    have h := hslow n N hn1 hnN
    rw [Real.div_rpow hNpos.le hnpos.le] at h
    calc (n : ℝ) ^ (-s) * mertensSaving n
        ≤ (n : ℝ) ^ (-s) * (K * mertensSaving N * ((N : ℝ) ^ η / (n : ℝ) ^ η)) := by
          gcongr
      _ = K * mertensSaving N * (N : ℝ) ^ η * ((n : ℝ) ^ (-s) / (n : ℝ) ^ η) := by ring
      _ = _ := by
          rw [← Real.rpow_sub hnpos]; ring_nf
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have hsum := sum_rpow_neg_head_le hc0 hc1 N
  have hE := mertensSaving_pos (N : ℝ)
  have hsplit : (N : ℝ) ^ η * (N : ℝ) ^ (1 - (s + η)) = (N : ℝ) ^ (1 - s) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hone : (N : ℝ) ^ η ≤ (N : ℝ) ^ (1 - s) * (K' * mertensSaving N) := by
    have h := hge N hN1
    have hpos : 0 < (N : ℝ) ^ η := Real.rpow_pos_of_pos hNpos _
    have e : (N : ℝ) ^ (1 - s) * (K'⁻¹ * (N : ℝ) ^ (-η)) = (N : ℝ) ^ η / K' := by
      rw [show (1 - s) = η + η by rw [hη_def]; ring, Real.rpow_add hNpos, Real.rpow_neg hNpos.le]
      field_simp
    have h2 : (N : ℝ) ^ η / K' ≤ (N : ℝ) ^ (1 - s) * mertensSaving N := by
      rw [← e]; gcongr
    calc (N : ℝ) ^ η = K' * ((N : ℝ) ^ η / K') := by field_simp
      _ ≤ K' * ((N : ℝ) ^ (1 - s) * mertensSaving N) := by gcongr
      _ = _ := by ring
  calc K * mertensSaving N * (N : ℝ) ^ η * ∑ i ∈ Icc 1 N, (i : ℝ) ^ (-(s + η))
      ≤ K * mertensSaving N * (N : ℝ) ^ η * (1 + (N : ℝ) ^ (1 - (s + η)) / (1 - (s + η))) := by
        gcongr
    _ = K * mertensSaving N * ((N : ℝ) ^ η +
          (N : ℝ) ^ η * (N : ℝ) ^ (1 - (s + η)) / (1 - (s + η))) := by ring
    _ ≤ K * mertensSaving N * ((N : ℝ) ^ (1 - s) * (K' * mertensSaving N) +
          (N : ℝ) ^ (1 - s) / (1 - (s + η))) := by
        rw [hsplit]; gcongr
    _ ≤ K * mertensSaving N * ((N : ℝ) ^ (1 - s) * K' + (N : ℝ) ^ (1 - s) / (1 - (s + η))) := by
        have hE1 : mertensSaving N ≤ 1 := by
          unfold mertensSaving deningerMertensSaving
          rw [Real.exp_le_one_iff, neg_nonpos]
          have := Real.log_nonneg hN1
          positivity
        gcongr
        exact mul_le_of_le_one_right hK'.le hE1
    _ = K * (1 / (1 - (s + η)) + K') * (N : ℝ) ^ (1 - s) * mertensSaving N := by ring

/-! ### The energy bound -/

theorem abelMertens_eq_mertensM (n : ℕ) : abelMertens n = Sieve.mertensM n := by
  unfold abelMertens prefixSum Sieve.mertensM
  rw [Finset.range_eq_Ico, show Finset.Ico 0 (n + 1) = insert 0 (Finset.Icc 1 n) by
    ext k; simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Icc]; omega,
    Finset.sum_insert (by simp)]
  simp

/-- `|M(n)| ≤ C n E(n)` for every `n ≥ 1`. -/
theorem exists_abs_abelMertens_le :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → |abelMertens n| ≤ C * n * mertensSaving n := by
  obtain ⟨B, hB, hrate⟩ := deningerMertensM_rate
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hrate
  set g : ℕ → ℝ := fun n => |abelMertens n| / ((n : ℝ) * mertensSaving n) with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by
    simp only [hg]; have := mertensSaving_pos (n : ℝ); positivity
  set C₀ : ℝ := ∑ n ∈ Finset.range n₀, g n with hC₀
  have hC0 : 0 ≤ C₀ := Finset.sum_nonneg fun n _ => hg0 n
  refine ⟨B + C₀ + 1, by linarith, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hE := mertensSaving_pos (n : ℝ)
  have hden : 0 < (n : ℝ) * mertensSaving n := mul_pos hn0 hE
  have hbig : (B + C₀ + 1) * n * mertensSaving n = B * (n * mertensSaving n) +
      (C₀ + 1) * (n * mertensSaving n) := by ring
  rcases le_or_gt n₀ n with h | h
  · have hb := hn₀ n h
    rw [abelMertens_eq_mertensM]
    have : B * n * deningerMertensSaving n = B * (n * mertensSaving n) := by
      unfold mertensSaving; ring
    rw [hbig]
    have : 0 ≤ (C₀ + 1) * (n * mertensSaving n) := by positivity
    linarith
  · have hle : g n ≤ C₀ := Finset.single_le_sum (fun n _ => hg0 n) (Finset.mem_range.mpr h)
    have hgn : g n * ((n : ℝ) * mertensSaving n) = |abelMertens n| := by
      simp only [hg]; field_simp
    rw [hbig]
    have h1 : |abelMertens n| ≤ C₀ * ((n : ℝ) * mertensSaving n) := by
      rw [← hgn]; exact mul_le_mul_of_nonneg_right hle hden.le
    have : 0 ≤ B * (n * mertensSaving n) := by positivity
    linarith

/-- `‖f_N‖_δ ≤ N^(-(1+δ)/2)`. -/
theorem gammaNorm_atom_le {δ : ℝ} (hδ : 0 ≤ δ) {N : ℝ} (hN : 0 < N) :
    gammaNorm δ (atom N) ≤ N ^ (-(1 + δ) / 2) := by
  have hδ' : 0 < 5 + δ := by linarith
  have hE : gammaEnergy δ (atom N) ≤ N ^ (-(1 + δ)) := by
    rw [gammaEnergy, gammaInner_atom hδ' hN hN, sourceKernel]
    rw [show N + N = 2 * N by ring, Real.mul_rpow (by norm_num) hN.le]
    have h2 : 1 ≤ (2 : ℝ) ^ (5 + δ) := Real.one_le_rpow (by norm_num) (by linarith)
    have hNp : 0 < N ^ (5 + δ) := Real.rpow_pos_of_pos hN _
    have e : N ^ (-(1 + δ)) = N ^ 4 / N ^ (5 + δ) := by
      rw [show (-(1 + δ)) = (4 : ℝ) - (5 + δ) by ring, Real.rpow_sub hN, Real.rpow_ofNat]
    rw [e, show N ^ 2 * N ^ 2 = N ^ 4 by ring]
    apply div_le_div_of_nonneg_left (by positivity) hNp
    nlinarith
  unfold gammaNorm
  calc Real.sqrt (gammaEnergy δ (atom N)) ≤ Real.sqrt (N ^ (-(1 + δ))) := Real.sqrt_le_sqrt hE
    _ = N ^ (-(1 + δ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN.le]; ring_nf

/-- `‖g_n‖_δ = ‖f_n - f_(n+1)‖_δ ≤ 4 C_1 n^(-(3+δ)/2)` for `n ≥ 1`, `0 ≤ δ ≤ 1`. -/
theorem gammaNorm_abelDipole_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {n : ℝ} (hn : 1 ≤ n) :
    gammaNorm δ (abelDipole n) ≤ 4 * jetConst 1 * n ^ (-(3 + δ) / 2) := by
  have hδ : 0 < 5 + δ := by linarith
  have hn0 : 0 < n := by linarith
  have e : abelDipole n = fun t => -(atom (n + 1) t - atom n t) := by
    funext t; unfold abelDipole; ring
  rw [e, gammaNorm_neg hδ ((gammaFinite_atom hδ (by linarith)).sub (gammaFinite_atom hδ hn0))]
  refine (gammaNorm_atom_sub_le hδ0 hδ1 hn0 (by linarith)).trans ?_
  have hC := jetConst_nonneg 1
  have hsq : (n + 1) ^ 2 ≤ 4 * n ^ 2 := by nlinarith
  have hpow : (n ^ ((5 + δ) / 2))⁻¹ / n = n ^ (-(3 + δ) / 2) / n ^ 2 := by
    rw [← Real.rpow_neg hn0.le]
    rw [show -(3 + δ) / 2 = -((5 + δ) / 2) + 1 by ring, Real.rpow_add_one hn0.ne']
    field_simp
  calc (n + 1 - n) * (jetConst 1 * (n + 1) ^ 2 * (n ^ ((5 + δ) / 2))⁻¹ / n)
      = jetConst 1 * (n + 1) ^ 2 * ((n ^ ((5 + δ) / 2))⁻¹ / n) := by ring
    _ = jetConst 1 * (n + 1) ^ 2 * (n ^ (-(3 + δ) / 2) / n ^ 2) := by rw [hpow]
    _ ≤ jetConst 1 * (4 * n ^ 2) * (n ^ (-(3 + δ) / 2) / n ^ 2) := by
        have : 0 ≤ n ^ (-(3 + δ) / 2) / n ^ 2 := by positivity
        gcongr
    _ = 4 * jetConst 1 * n ^ (-(3 + δ) / 2) := by field_simp

/-- **The Mertens energy bound.**  For `0 ≤ δ < 1` there is `C` with
`‖S_N‖_δ ≤ C N^((1-δ)/2) E(N)` for every cutoff `N ≥ 1`. -/
theorem gammaNorm_mobiusCubicSource_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      gammaNorm δ (mobiusCubicSource N) ≤ C * (N : ℝ) ^ ((1 - δ) / 2) * mertensSaving N := by
  have hδ : 0 < 5 + δ := by linarith
  obtain ⟨CM, hCM, hM⟩ := exists_abs_abelMertens_le
  obtain ⟨CS, hCS, hS⟩ := sum_rpow_neg_mul_mertensSaving_le (s := (1 + δ) / 2) (by linarith)
    (by linarith)
  have hj := jetConst_nonneg 1
  refine ⟨CM + CM * 4 * jetConst 1 * CS, by positivity, fun N hN => ?_⟩
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
  set Nr : ℝ := ((K + 1 : ℕ) : ℝ) with hNr
  have hN1 : (1 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast (by omega : 1 ≤ K + 1)
  have hN0 : 0 < Nr := by linarith
  have hENr := mertensSaving_pos Nr
  have hpos : ∀ n ∈ Icc 1 K, (1 : ℝ) ≤ n := fun n hn => by exact_mod_cast (mem_Icc.mp hn).1
  have hfin : ∀ n ∈ Icc 1 K, GammaFinite δ (fun t => abelMertens n * abelDipole n t) :=
    fun n hn => (gammaFinite_abelDipole hδ (by linarith [hpos n hn])).smul _
  have heq : mobiusCubicSource (K + 1) = fun t => abelMertens (K + 1) * atom Nr t +
      ∑ n ∈ Icc 1 K, abelMertens n * abelDipole n t := by
    funext t; exact mobiusCubicSource_eq_abel K t
  -- the terminal term
  have hT : gammaNorm δ (fun t => abelMertens (K + 1) * atom Nr t) ≤
      CM * Nr ^ ((1 - δ) / 2) * mertensSaving Nr := by
    rw [gammaNorm_smul hδ (gammaFinite_atom hδ hN0)]
    calc |abelMertens (K + 1)| * gammaNorm δ (atom Nr)
        ≤ (CM * Nr * mertensSaving Nr) * Nr ^ (-(1 + δ) / 2) :=
          mul_le_mul (hM (K + 1) (by omega)) (gammaNorm_atom_le hδ0 hN0) (gammaNorm_nonneg _ _)
            (by positivity)
      _ = CM * Nr ^ ((1 - δ) / 2) * mertensSaving Nr := by
          rw [show (1 - δ) / 2 = -(1 + δ) / 2 + 1 by ring, Real.rpow_add_one hN0.ne']
          ring
  -- the dipole terms
  have hD : ∀ n ∈ Icc 1 K, gammaNorm δ (fun t => abelMertens n * abelDipole n t) ≤
      CM * 4 * jetConst 1 * ((n : ℝ) ^ (-((1 + δ) / 2)) * mertensSaving n) := by
    intro n hn
    have hn1 := hpos n hn
    have hn0 : (0 : ℝ) < n := by linarith
    rw [gammaNorm_smul hδ (gammaFinite_abelDipole hδ hn0)]
    calc |abelMertens n| * gammaNorm δ (abelDipole n)
        ≤ (CM * n * mertensSaving n) * (4 * jetConst 1 * (n : ℝ) ^ (-(3 + δ) / 2)) :=
          mul_le_mul (hM n (mem_Icc.mp hn).1) (gammaNorm_abelDipole_le hδ0 hδ1.le hn1)
            (gammaNorm_nonneg _ _) (by have := mertensSaving_pos (n : ℝ); positivity)
      _ = CM * 4 * jetConst 1 * ((n : ℝ) ^ (-((1 + δ) / 2)) * mertensSaving n) := by
          rw [show (-((1 + δ) / 2)) = -(3 + δ) / 2 + 1 by ring, Real.rpow_add_one hn0.ne']
          ring
  have hsub : ∑ n ∈ Icc 1 K, (n : ℝ) ^ (-((1 + δ) / 2)) * mertensSaving n ≤
      ∑ n ∈ Icc 1 (K + 1), (n : ℝ) ^ (-((1 + δ) / 2)) * mertensSaving n :=
    sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl (by omega))
      (fun n _ _ => by have := mertensSaving_pos (n : ℝ); positivity)
  have hSK := hS (K + 1) (by omega)
  rw [show 1 - (1 + δ) / 2 = (1 - δ) / 2 by ring] at hSK
  have hsumD : gammaNorm δ (fun t => ∑ n ∈ Icc 1 K, abelMertens n * abelDipole n t) ≤
      CM * 4 * jetConst 1 * (CS * Nr ^ ((1 - δ) / 2) * mertensSaving Nr) := by
    refine (gammaNorm_sum_le hδ _ hfin).trans ((sum_le_sum hD).trans ?_)
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (hsub.trans hSK) (by positivity)
  rw [heq]
  refine (gammaNorm_add_le hδ ((gammaFinite_atom hδ hN0).smul _) (GammaFinite.sum _ hfin)).trans ?_
  have := add_le_add hT hsumD
  refine this.trans (le_of_eq ?_)
  ring

end RHTower.CubicGamma
