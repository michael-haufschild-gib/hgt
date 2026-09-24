import GaloisForLFunctions.RHTower.HighBlockParameters

/-!
# The sharp-cutoff energy at head length one

`SharpEnergyInput C` asks for a bound `C`, uniform in the head length `u`, on the coefficient energy
of a sharp head of the direct sum `Σ n^{-1/2-it}` against the displaced Barban–Vehov mollifier
`b_d(m) = μ(m) log(N/m)/log N · m^{-1/2+d}`.

At `u = 0` the head is the single term `1`, so that energy is exactly the mollifier's own displaced
coefficient energy

```text
E(0,d) = Σ_{m ≤ N} (μ(m) log(N/m) / log N)² · m^{2d-1}.
```

Restricting to primes `p` with `p² ≤ N`, where the Barban–Vehov ratio is at least `1/2` and
`m^{2d-1} ≥ 1/m`, gives `E(0,d) ≥ ¼ Σ_{p ≤ √N} 1/p`, which is unbounded because the prime
reciprocal series diverges.  Hence no constant satisfies `SharpEnergyInput C`.

In the other direction `E(0,d) ≤ N^{2d} Σ_{m ≤ N} 1/m`, so the head-one energy has exactly the size
of the harmonic sum of the mollifier length, inflated by the displacement factor `N^{2d}`.  The
obstruction is therefore not the mollifier but the sharp cutoff: at head length one the head no
longer carries the cancellation between `ζ` and its mollifier, and the surviving quantity is a
harmonic sum.
-/

open Complex Finset Filter

namespace RHTower

noncomputable section

/-- A sharp head of length one selects the right factor of a Dirichlet convolution. -/
theorem dirConv_sharpHead_zero {L N : ℕ} (hL : 1 ≤ L) (h : ℕ → ℂ) (b : Fin N → ℂ)
    (r : Fin (L * N)) :
    Sieve.dirConv L N (sharpHead h L 0) b r
      = if hr : (r : ℕ) < N then h 0 * b ⟨(r : ℕ), hr⟩ else 0 := by
  classical
  unfold Sieve.dirConv sharpHead
  by_cases hr : (r : ℕ) < N
  · rw [dif_pos hr]
    have hmem : ((⟨0, hL⟩ : Fin L), (⟨(r : ℕ), hr⟩ : Fin N)) ∈
        (Finset.univ : Finset (Fin L × Fin N)).filter
          (fun q => ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) = (r : ℕ) + 1) := by
      simp
    rw [Finset.sum_eq_single_of_mem _ hmem]
    · simp
    · intro q hq hqne
      rw [Finset.mem_filter] at hq
      have hq1 : (q.1 : ℕ) ≠ 0 := by
        intro h0
        refine hqne (Prod.ext (Fin.ext h0) (Fin.ext ?_))
        show (q.2 : ℕ) = (r : ℕ)
        have h2 := hq.2
        rw [h0] at h2
        simp only [zero_add, one_mul] at h2
        omega
      simp [hq1]
  · rw [dif_neg hr]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Finset.mem_filter] at hq
    have hq1 : (q.1 : ℕ) ≠ 0 := by
      intro h0
      have h2 := hq.2
      rw [h0] at h2
      simp only [zero_add, one_mul] at h2
      have hlt : (q.2 : ℕ) < N := q.2.isLt
      omega
    simp [hq1]

/-- The displaced mollifier coefficient has squared modulus `(mu(m) log(N/m)/log N)^2 m^(2d-1)`. -/
theorem norm_highBlockMollifierCoeffNat_sq (d : ℝ) (N m : ℕ) :
    ‖highBlockMollifierCoeffNat d (hbCoeff N) m‖ ^ 2
      = (Sieve.barbanVehovWeight N (m + 1) / Real.log N) ^ 2 * (((m : ℝ) + 1) ^ (2 * d - 1)) := by
  unfold highBlockMollifierCoeffNat hbCoeff
  rw [norm_mul, mul_pow]
  congr 1
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hcast : ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.neg_re, displacedLinePt_re,
      ← Real.rpow_natCast (((m : ℝ) + 1) ^ (-(1 / 2 - d))) 2, ← Real.rpow_mul hpos.le]
    congr 1
    push_cast
    ring

/-- **Head length one.** The sharp-cutoff energy at `u = 0` is exactly the mollifier's own
displaced coefficient energy. -/
theorem sharpEnergy_head_one_eq (d : ℝ) {L N : ℕ} (hL : 1 ≤ L) :
    (∑ r : Fin (L * N),
      ‖Sieve.dirConv L N (sharpHead criticalHeadCoeff L 0)
          (fun m => highBlockMollifierCoeffNat d (hbCoeff N) m) r‖ ^ 2)
      = ∑ m ∈ Finset.Icc 1 N,
          (Sieve.barbanVehovWeight N m / Real.log N) ^ 2 * ((m : ℝ) ^ (2 * d - 1)) := by
  classical
  have hhead : criticalHeadCoeff 0 = 1 := by
    unfold criticalHeadCoeff
    norm_num
  set F : ℕ → ℝ := fun i =>
    if i < N then ‖highBlockMollifierCoeffNat d (hbCoeff N) i‖ ^ 2 else 0 with hF
  have hpt : ∀ r : Fin (L * N),
      ‖Sieve.dirConv L N (sharpHead criticalHeadCoeff L 0)
          (fun m => highBlockMollifierCoeffNat d (hbCoeff N) m) r‖ ^ 2 = F (r : ℕ) := by
    intro r
    rw [dirConv_sharpHead_zero hL]
    by_cases hr : (r : ℕ) < N
    · rw [dif_pos hr, hF]
      simp [hr, hhead]
    · rw [dif_neg hr, hF]
      simp [hr]
  rw [Finset.sum_congr rfl (fun r _ => hpt r), Fin.sum_univ_eq_sum_range F (L * N)]
  have hNle : N ≤ L * N := by
    calc N = 1 * N := (one_mul N).symm
      _ ≤ L * N := Nat.mul_le_mul_right N hL
  have hsub : Finset.range N ⊆ Finset.range (L * N) := fun i hi =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hNle)
  have hout : ∀ i ∈ Finset.range (L * N), i ∉ Finset.range N → F i = 0 := by
    intro i _ hi
    rw [Finset.mem_range] at hi
    simp [hF, hi]
  rw [← Finset.sum_subset hsub hout]
  have hin : ∀ i ∈ Finset.range N, F i = ‖highBlockMollifierCoeffNat d (hbCoeff N) i‖ ^ 2 := by
    intro i hi
    rw [Finset.mem_range] at hi
    simp [hF, hi]
  rw [Finset.sum_congr rfl hin]
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_highBlockMollifierCoeffNat_sq]
  rw [show 1 + i = i + 1 from Nat.add_comm 1 i]
  push_cast
  ring

/-- Nonnegativity of the head-one energy terms. -/
theorem headOneTerm_nonneg (d : ℝ) (N m : ℕ) :
    0 ≤ (Sieve.barbanVehovWeight N m / Real.log N) ^ 2 * ((m : ℝ) ^ (2 * d - 1)) := by
  have h1 : (0 : ℝ) ≤ (Sieve.barbanVehovWeight N m / Real.log N) ^ 2 := sq_nonneg _
  have h2 : (0 : ℝ) ≤ (m : ℝ) ^ (2 * d - 1) := Real.rpow_nonneg (Nat.cast_nonneg m) _
  exact mul_nonneg h1 h2

/-- A prime `p` with `p^2 ≤ N` contributes at least `1/(4p)` to the head-one energy. -/
theorem quarter_inv_le_headOneTerm {d : ℝ} (hd : 0 < d) {N p : ℕ} (hp : Nat.Prime p)
    (hpN : p * p ≤ N) :
    (1 / 4 : ℝ) * (1 / (p : ℝ))
      ≤ (Sieve.barbanVehovWeight N p / Real.log N) ^ 2 * ((p : ℝ) ^ (2 * d - 1)) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpNle : p ≤ N := le_trans (Nat.le_mul_of_pos_left p (by omega)) hpN
  have hN4 : 4 ≤ N := le_trans (by nlinarith) hpN
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hNR : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
  -- the squared Barban-Vehov ratio is at least `1/4`
  have hsq : (1 / 4 : ℝ) ≤ (Sieve.barbanVehovWeight N p / Real.log N) ^ 2 := by
    have hw : Sieve.barbanVehovWeight N p = -Real.log ((N : ℝ) / (p : ℝ)) := by
      unfold Sieve.barbanVehovWeight
      rw [if_pos hpNle, ArithmeticFunction.moebius_apply_prime hp]
      push_cast
      ring
    have hpp : (p : ℝ) * (p : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpN
    have hlog2p : 2 * Real.log p ≤ Real.log N := by
      have : Real.log ((p : ℝ) * (p : ℝ)) ≤ Real.log N :=
        Real.log_le_log (by positivity) hpp
      rwa [Real.log_mul (by positivity) (by positivity), ← two_mul] at this
    have hdiv : Real.log ((N : ℝ) / (p : ℝ)) = Real.log N - Real.log p :=
      Real.log_div (by positivity) (by positivity)
    have hhalf : Real.log N / 2 ≤ Real.log ((N : ℝ) / (p : ℝ)) := by
      rw [hdiv]; linarith
    have hratio : (1 / 2 : ℝ) ≤ Real.log ((N : ℝ) / (p : ℝ)) / Real.log N := by
      rw [le_div_iff₀ hlogN]; linarith
    have : Sieve.barbanVehovWeight N p / Real.log N
        = -(Real.log ((N : ℝ) / (p : ℝ)) / Real.log N) := by rw [hw]; ring
    rw [this, neg_sq]
    nlinarith [hratio]
  -- the displaced power is at least `1/p`
  have hpow : (1 : ℝ) / (p : ℝ) ≤ (p : ℝ) ^ (2 * d - 1) := by
    have h1p : (1 : ℝ) ≤ (p : ℝ) := by linarith
    have hexp : (-1 : ℝ) ≤ 2 * d - 1 := by linarith
    have hr := Real.rpow_le_rpow_of_exponent_le h1p hexp
    rw [Real.rpow_neg_one] at hr
    rwa [one_div]
  have hinvpos : (0 : ℝ) < 1 / (p : ℝ) := by positivity
  calc (1 / 4 : ℝ) * (1 / (p : ℝ))
      ≤ (Sieve.barbanVehovWeight N p / Real.log N) ^ 2 * (1 / (p : ℝ)) :=
        mul_le_mul_of_nonneg_right hsq hinvpos.le
    _ ≤ (Sieve.barbanVehovWeight N p / Real.log N) ^ 2 * ((p : ℝ) ^ (2 * d - 1)) :=
        mul_le_mul_of_nonneg_left hpow (sq_nonneg _)

/-- A quarter of the prime reciprocal sum up to `sqrt N` bounds the head-one energy below. -/
theorem quarter_primeSum_le_headOneEnergy {d : ℝ} (hd : 0 < d) {N X : ℕ} (hX : X * X ≤ N) :
    (1 / 4 : ℝ) * (∑ i ∈ Finset.range X,
        Set.indicator {p : ℕ | Nat.Prime p} (fun n : ℕ => 1 / (n : ℝ)) i)
      ≤ ∑ m ∈ Finset.Icc 1 N,
          (Sieve.barbanVehovWeight N m / Real.log N) ^ 2 * ((m : ℝ) ^ (2 * d - 1)) := by
  classical
  have hsq : ∀ i ∈ Finset.range X, Nat.Prime i → i * i ≤ N := by
    intro i hi hp
    have hiX : i < X := Finset.mem_range.mp hi
    exact le_trans (Nat.mul_le_mul hiX.le hiX.le) hX
  have hind : ∀ i : ℕ, Set.indicator {p : ℕ | Nat.Prime p} (fun n : ℕ => 1 / (n : ℝ)) i
      = if Nat.Prime i then 1 / (i : ℝ) else 0 := by
    intro i
    rw [Set.indicator_apply]
    rfl
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun i _ => by rw [hind i])]
  have hstep : ∀ i ∈ Finset.range X,
      (1 / 4 : ℝ) * (if Nat.Prime i then 1 / (i : ℝ) else 0)
        ≤ if Nat.Prime i then
            (Sieve.barbanVehovWeight N i / Real.log N) ^ 2 * ((i : ℝ) ^ (2 * d - 1)) else 0 := by
    intro i hi
    by_cases hp : Nat.Prime i
    · rw [if_pos hp, if_pos hp]
      exact quarter_inv_le_headOneTerm hd hp (hsq i hi hp)
    · rw [if_neg hp, if_neg hp, mul_zero]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => headOneTerm_nonneg d N m)
  intro i hi
  rw [Finset.mem_filter] at hi
  obtain ⟨hiX, hp⟩ := hi
  have hii := hsq i hiX hp
  exact Finset.mem_Icc.mpr ⟨hp.one_lt.le.trans' (by norm_num),
    le_trans (Nat.le_mul_of_pos_left i hp.pos) hii⟩

/-- **The sharp-energy input has no constant.**  At head length one the sharp-cutoff energy is the
displaced mollifier energy, which already exceeds a quarter of the prime reciprocal sum up to
`sqrt N` and is therefore unbounded as the mollifier length grows. -/
theorem not_sharpEnergyInput (C : ℝ) : ¬ SharpEnergyInput C := by
  classical
  intro hin
  have hnn : ∀ n : ℕ,
      0 ≤ Set.indicator {p : ℕ | Nat.Prime p} (fun n : ℕ => 1 / (n : ℝ)) n := by
    intro n
    refine Set.indicator_nonneg (fun a _ => ?_) n
    positivity
  have htend : Filter.Tendsto
      (fun n => ∑ i ∈ Finset.range n,
        Set.indicator {p : ℕ | Nat.Prime p} (fun n : ℕ => 1 / (n : ℝ)) i)
      Filter.atTop Filter.atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp not_summable_one_div_on_primes
  obtain ⟨X, hXsum⟩ : ∃ X : ℕ, 4 * C + 1 ≤ ∑ i ∈ Finset.range X,
      Set.indicator {p : ℕ | Nat.Prime p} (fun n : ℕ => 1 / (n : ℝ)) i :=
    (htend.eventually_ge_atTop (4 * C + 1)).exists
  obtain ⟨U, ⟨hUin, hUV⟩, hU1⟩ :=
    ((hin.and (Filter.eventually_ge_atTop (((X * X + 2 : ℕ) : ℝ) ^ (20 : ℕ)))).and
      (Filter.eventually_ge_atTop (1 : ℝ))).exists
  -- the mollifier length exceeds `X^2`
  have hXXN : X * X ≤ hbN U := by
    have h1 : (((X * X + 2 : ℕ) : ℝ) ^ (20 : ℕ)) ^ ((1 : ℝ) / 20) ≤ U ^ ((1 : ℝ) / 20) :=
      Real.rpow_le_rpow (by positivity) hUV (by norm_num)
    have h2 : (((X * X + 2 : ℕ) : ℝ) ^ (20 : ℕ)) ^ ((1 : ℝ) / 20) = ((X * X + 2 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast (((X * X + 2 : ℕ) : ℝ)) 20, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [h2] at h1
    have h3 := hbN_gt (U := U)
    have h4 : ((X * X : ℕ) : ℝ) + 1 < (hbN U : ℝ) := by push_cast at h1 h3 ⊢; linarith
    have h5 : X * X + 1 < hbN U := by exact_mod_cast h4
    omega
  have hL1 : 1 ≤ hbL 1 := hbL_pos le_rfl
  have hbound := hUin (1 / 4) (by norm_num) (by norm_num) 1 le_rfl hU1 0
    (Finset.mem_range.mpr hL1)
  rw [sharpEnergy_head_one_eq (1 / 4) hL1] at hbound
  have hlow := quarter_primeSum_le_headOneEnergy (d := 1 / 4) (by norm_num)
    (N := hbN U) (X := X) hXXN
  have hmul : (1 / 4 : ℝ) * (4 * C + 1) ≤ (1 / 4 : ℝ) * (∑ i ∈ Finset.range X,
      Set.indicator {p : ℕ | Nat.Prime p} (fun n : ℕ => 1 / (n : ℝ)) i) := by
    exact mul_le_mul_of_nonneg_left hXsum (by norm_num)
  linarith

/-- **The head-one energy is at most the displaced harmonic sum.**  Together with the prime lower
bound this fixes its order: the sharp-cutoff energy at head length one is the harmonic sum of the
mollifier length, inflated by the displacement factor `N^{2d}`. -/
theorem headOneEnergy_le {d : ℝ} (hd : 0 ≤ d) {N : ℕ} (hN : 2 ≤ N) :
    (∑ m ∈ Finset.Icc 1 N,
        (Sieve.barbanVehovWeight N m / Real.log N) ^ 2 * ((m : ℝ) ^ (2 * d - 1)))
      ≤ (N : ℝ) ^ (2 * d) * ∑ m ∈ Finset.Icc 1 N, ((m : ℝ))⁻¹ := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hmNR : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
  have hcoeff : (Sieve.barbanVehovWeight N m / Real.log N) ^ 2 ≤ 1 := by
    have h := norm_hbCoeff_le hN hm
    unfold hbCoeff at h
    rw [Complex.norm_real, Real.norm_eq_abs] at h
    nlinarith [abs_nonneg (Sieve.barbanVehovWeight N m / Real.log N),
      sq_abs (Sieve.barbanVehovWeight N m / Real.log N)]
  have hsplit : (m : ℝ) ^ (2 * d - 1) = (m : ℝ) ^ (2 * d) * ((m : ℝ))⁻¹ := by
    rw [show 2 * d - 1 = 2 * d + (-1) by ring, Real.rpow_add hm0, Real.rpow_neg_one]
  have hpow : (m : ℝ) ^ (2 * d) ≤ (N : ℝ) ^ (2 * d) :=
    Real.rpow_le_rpow hm0.le hmNR (by linarith)
  have hinv : (0 : ℝ) < ((m : ℝ))⁻¹ := by positivity
  calc (Sieve.barbanVehovWeight N m / Real.log N) ^ 2 * ((m : ℝ) ^ (2 * d - 1))
      ≤ 1 * ((m : ℝ) ^ (2 * d - 1)) :=
        mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hm0.le _)
    _ = (m : ℝ) ^ (2 * d) * ((m : ℝ))⁻¹ := by rw [one_mul, hsplit]
    _ ≤ (N : ℝ) ^ (2 * d) * ((m : ℝ))⁻¹ := mul_le_mul_of_nonneg_right hpow hinv.le

end

end RHTower
