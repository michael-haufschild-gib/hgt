import GaloisForLFunctions.HTGeometry.FiniteRangeProjectiveTail

/-!
# Prime exponential-polynomial fibre rigidity

The finite-range shift--jet law of `FiniteRangeProjectiveTail` carries an explicit boundary
hypothesis `FactorClockFiberIndependent factor clock m`: no nonzero linear combination of the
shift--clock monomials may vanish off a finite subset of an infinite coordinate fibre.  This module
discharges that hypothesis for the genuine prime-Dirichlet columns

`factor a p = exp(-α a · log p) = p^{-α a}`,  `clock p = log p`,

whenever the finite shifts `α a` have pairwise distinct real parts, at every finite jet order and on
every infinite subset of the primes.

The mechanism is the classical dominance of finite exponential-polynomial sums.  Writing the tested
identity along an unbounded sequence `L = log p → +∞`, one groups the columns by shift into
`∑ₐ Qₐ(L) · e^{-α a·L}` with `Qₐ` a polynomial in `L`.  Peeling the shift of least real part and
dividing by its exponential, every other block decays exponentially against every power of `L`, so
the surviving polynomial block tends to `0` on an unbounded set and is therefore identically zero;
iterating over the finite shift set kills all coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- A positive exponential rate beats every fixed power: `xᵏ · e^{-δx} → 0`. -/
theorem tendsto_pow_mul_exp_neg_mul {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ k * Real.exp (-(δ * x))) atTop (𝓝 0) := by
  have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
  have hφ : Tendsto (fun x : ℝ => δ * x) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hδ tendsto_id
  have hcomp := hbase.comp hφ
  have hconst := hcomp.const_mul ((δ ^ k)⁻¹)
  simp only [mul_zero] at hconst
  refine hconst.congr ?_
  intro x
  have hx : ((δ * x) ^ k) = δ ^ k * x ^ k := by rw [mul_pow]
  rw [Function.comp_apply, hx]
  field_simp

/-- **Finite complex polynomial vanishing at infinity.**  If a finite `ℂ`-linear polynomial in a
real variable tends to `0` along a sequence `u n → +∞`, all its coefficients vanish.  Proof by
stripping the constant term: `(S − e₀)/u` has degree one lower and still tends to `0`. -/
theorem finpoly_coeffs_zero_of_tendsto :
    ∀ (m : ℕ) (e : ℕ → ℂ) (u : ℕ → ℝ),
      Tendsto u atTop atTop →
      Tendsto (fun n => ∑ k ∈ Finset.range (m + 1), e k * (u n : ℂ) ^ k) atTop (𝓝 0) →
      ∀ k < m + 1, e k = 0 := by
  intro m
  induction m with
  | zero =>
      intro e u _ h k hk
      interval_cases k
      have hconst : Tendsto (fun _ : ℕ => e 0) atTop (𝓝 (e 0)) := tendsto_const_nhds
      have hval : (fun n => ∑ k ∈ Finset.range (0 + 1), e k * (u n : ℂ) ^ k) = fun _ => e 0 := by
        funext n; simp
      rw [hval] at h
      exact tendsto_nhds_unique hconst h
  | succ m ih =>
      intro e u hu h
      have hunorm : Tendsto (fun n => |u n|) atTop atTop :=
        tendsto_atTop_mono (fun n => le_abs_self (u n)) hu
      set R : ℕ → ℂ := fun n => ∑ k ∈ Finset.range (m + 1), e (k + 1) * (u n : ℂ) ^ k with hR
      have hsplit : ∀ n, (∑ k ∈ Finset.range (m + 1 + 1), e k * (u n : ℂ) ^ k)
          = (u n : ℂ) * R n + e 0 := by
        intro n
        rw [Finset.sum_range_succ' (fun k => e k * (u n : ℂ) ^ k) (m + 1)]
        simp only [pow_zero, mul_one, hR]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [pow_succ]; ring
      have hinv : Tendsto (fun n => (u n : ℂ)⁻¹) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hn : (fun n => ‖(u n : ℂ)⁻¹‖) = fun n => |u n|⁻¹ := by
          funext n; rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
        rw [hn]
        exact hunorm.inv_tendsto_atTop
      have hSe0 : Tendsto (fun n => (∑ k ∈ Finset.range (m + 1 + 1), e k * (u n : ℂ) ^ k) - e 0)
          atTop (𝓝 (0 - e 0)) := h.sub tendsto_const_nhds
      have hReq : ∀ᶠ n in atTop,
          R n = ((∑ k ∈ Finset.range (m + 1 + 1), e k * (u n : ℂ) ^ k) - e 0) * (u n : ℂ)⁻¹ := by
        filter_upwards [hu.eventually_gt_atTop 0] with n hn
        have hune : (u n : ℂ) ≠ 0 := by
          simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hn
        rw [hsplit n]
        field_simp
        ring
      have hRtend : Tendsto R atTop (𝓝 0) := by
        have hprod := hSe0.mul hinv
        simp only [mul_zero] at hprod
        exact hprod.congr' (hReq.mono (fun n hn => hn.symm))
      have hIH : ∀ k < m + 1, e (k + 1) = 0 := ih (fun k => e (k + 1)) u hu hRtend
      have hS0 : Tendsto (fun _ : ℕ => e 0) atTop (𝓝 0) := by
        refine h.congr ?_
        intro n
        rw [hsplit n]
        have hRn : R n = 0 := by
          rw [hR]; apply Finset.sum_eq_zero; intro k hk
          rw [hIH k (Finset.mem_range.mp hk), zero_mul]
        rw [hRn, mul_zero, zero_add]
      have he0 : e 0 = 0 := tendsto_nhds_unique tendsto_const_nhds hS0
      intro k hk
      match k, hk with
      | 0, _ => exact he0
      | (j + 1), hk => exact hIH j (by omega)

variable {A : Type*} [DecidableEq A]

/-- **Shift-peeling rigidity (sequence form).**  A finite exponential-polynomial family with
pairwise distinct shift real parts, tested along a clock sequence `u n → +∞`, has only the trivial
coefficient system. -/
theorem expPoly_rigidity (m : ℕ) (alpha : A → ℂ) (d : A → ℕ → ℂ) (u : ℕ → ℝ)
    (hu : Tendsto u atTop atTop) :
    ∀ (s : Finset A),
      (∀ a ∈ s, ∀ b ∈ s, (alpha a).re = (alpha b).re → a = b) →
      (∀ n, ∑ a ∈ s, (∑ k ∈ Finset.range (m + 1), d a k * (u n : ℂ) ^ k)
          * Complex.exp (-(alpha a) * (u n : ℂ)) = 0) →
      ∀ a ∈ s, ∀ k < m + 1, d a k = 0 := by
  intro s
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro hdist hzero
    rcases s.eq_empty_or_nonempty with rfl | hne
    · intro a ha; exact absurd ha (Finset.notMem_empty a)
    obtain ⟨a₀, ha₀, hmin⟩ := Finset.exists_min_image s (fun a => (alpha a).re) hne
    set T : A → ℕ → ℂ := fun a n =>
      (∑ k ∈ Finset.range (m + 1), d a k * (u n : ℂ) ^ k)
        * Complex.exp ((alpha a₀ - alpha a) * (u n : ℂ)) with hT
    have hexp : ∀ a n, Complex.exp (alpha a₀ * (u n : ℂ)) * Complex.exp (-(alpha a) * (u n : ℂ))
        = Complex.exp ((alpha a₀ - alpha a) * (u n : ℂ)) := by
      intro a n; rw [← Complex.exp_add]; congr 1; ring
    have hmul : ∀ n, ∑ a ∈ s, T a n = 0 := by
      intro n
      have hstep : ∑ a ∈ s, T a n
          = Complex.exp (alpha a₀ * (u n : ℂ)) *
              ∑ a ∈ s, (∑ k ∈ Finset.range (m + 1), d a k * (u n : ℂ) ^ k)
                * Complex.exp (-(alpha a) * (u n : ℂ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        simp only [hT]
        rw [← hexp a n]; ring
      rw [hstep, hzero n, mul_zero]
    have hT0 : ∀ n, T a₀ n = ∑ k ∈ Finset.range (m + 1), d a₀ k * (u n : ℂ) ^ k := by
      intro n; simp only [hT, sub_self, zero_mul, Complex.exp_zero, mul_one]
    have hQ0 : ∀ n, (∑ k ∈ Finset.range (m + 1), d a₀ k * (u n : ℂ) ^ k)
        = -∑ a ∈ s.erase a₀, T a n := by
      intro n
      have hs : T a₀ n + ∑ a ∈ s.erase a₀, T a n = ∑ a ∈ s, T a n :=
        Finset.add_sum_erase s (fun a => T a n) ha₀
      rw [hmul n] at hs
      rw [hT0 n] at hs
      linear_combination hs
    have hterm : ∀ a ∈ s.erase a₀, Tendsto (fun n => T a n) atTop (𝓝 0) := by
      intro a ha
      have hasin : a ∈ s := Finset.mem_of_mem_erase ha
      have hane : a ≠ a₀ := Finset.ne_of_mem_erase ha
      have hle : (alpha a₀).re ≤ (alpha a).re := hmin a hasin
      have hne' : (alpha a₀).re ≠ (alpha a).re := fun heq => hane (hdist a hasin a₀ ha₀ heq.symm)
      have hδ : 0 < (alpha a).re - (alpha a₀).re := by
        rcases lt_or_eq_of_le hle with h | h
        · linarith
        · exact absurd h hne'
      set δ : ℝ := (alpha a).re - (alpha a₀).re with hδdef
      have hgtend : Tendsto (fun n => ∑ k ∈ Finset.range (m + 1),
          ‖d a k‖ * ((u n) ^ k * Real.exp (-(δ * u n)))) atTop (𝓝 0) := by
        have hg' : Tendsto (fun n => ∑ k ∈ Finset.range (m + 1),
            ‖d a k‖ * ((u n) ^ k * Real.exp (-(δ * u n)))) atTop
            (𝓝 (∑ _k ∈ Finset.range (m + 1), (0 : ℝ))) := by
          apply tendsto_finsetSum
          intro k _
          have hk := ((tendsto_pow_mul_exp_neg_mul hδ k).comp hu).const_mul (‖d a k‖)
          simpa [Function.comp] using hk
        simpa using hg'
      refine squeeze_zero_norm' ?_ hgtend
      filter_upwards [hu.eventually_ge_atTop 0] with n hn
      have hnormexp : ‖Complex.exp ((alpha a₀ - alpha a) * (u n : ℂ))‖ = Real.exp (-(δ * u n)) := by
        rw [Complex.norm_exp]
        congr 1
        simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
          Complex.ofReal_im, mul_zero, sub_zero, hδdef]
        ring
      have hnormQ : ‖∑ k ∈ Finset.range (m + 1), d a k * (u n : ℂ) ^ k‖
          ≤ ∑ k ∈ Finset.range (m + 1), ‖d a k‖ * (u n) ^ k := by
        refine le_trans (norm_sum_le _ _) ?_
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
      calc ‖T a n‖
          = ‖∑ k ∈ Finset.range (m + 1), d a k * (u n : ℂ) ^ k‖ * Real.exp (-(δ * u n)) := by
              simp only [hT]; rw [norm_mul, hnormexp]
        _ ≤ (∑ k ∈ Finset.range (m + 1), ‖d a k‖ * (u n) ^ k) * Real.exp (-(δ * u n)) :=
              mul_le_mul_of_nonneg_right hnormQ (le_of_lt (Real.exp_pos _))
        _ = ∑ k ∈ Finset.range (m + 1), ‖d a k‖ * ((u n) ^ k * Real.exp (-(δ * u n))) := by
              rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; ring
    have hQ0tend : Tendsto (fun n => ∑ k ∈ Finset.range (m + 1), d a₀ k * (u n : ℂ) ^ k)
        atTop (𝓝 0) := by
      have hsumtend : Tendsto (fun n => ∑ a ∈ s.erase a₀, T a n) atTop (𝓝 0) := by
        have hfin := tendsto_finsetSum (s.erase a₀) hterm
        simpa using hfin
      have hneg := hsumtend.neg
      simp only [neg_zero] at hneg
      exact hneg.congr (fun n => (hQ0 n).symm)
    have hda₀ : ∀ k < m + 1, d a₀ k = 0 :=
      finpoly_coeffs_zero_of_tendsto m (d a₀) u hu hQ0tend
    have hzero_erase : ∀ n, ∑ a ∈ s.erase a₀,
        (∑ k ∈ Finset.range (m + 1), d a k * (u n : ℂ) ^ k)
          * Complex.exp (-(alpha a) * (u n : ℂ)) = 0 := by
      intro n
      have hs : (∑ k ∈ Finset.range (m + 1), d a₀ k * (u n : ℂ) ^ k)
            * Complex.exp (-(alpha a₀) * (u n : ℂ))
          + ∑ a ∈ s.erase a₀, (∑ k ∈ Finset.range (m + 1), d a k * (u n : ℂ) ^ k)
              * Complex.exp (-(alpha a) * (u n : ℂ))
          = ∑ a ∈ s, (∑ k ∈ Finset.range (m + 1), d a k * (u n : ℂ) ^ k)
              * Complex.exp (-(alpha a) * (u n : ℂ)) :=
        Finset.add_sum_erase s (fun a => (∑ k ∈ Finset.range (m + 1), d a k * (u n : ℂ) ^ k)
          * Complex.exp (-(alpha a) * (u n : ℂ))) ha₀
      rw [hzero n] at hs
      have hz0 : (∑ k ∈ Finset.range (m + 1), d a₀ k * (u n : ℂ) ^ k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [hda₀ k (Finset.mem_range.mp hk), zero_mul]
      rw [hz0, zero_mul, zero_add] at hs
      exact hs
    have hdist_erase : ∀ a ∈ s.erase a₀, ∀ b ∈ s.erase a₀,
        (alpha a).re = (alpha b).re → a = b :=
      fun a ha b hb => hdist a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
    have hrest := ih (s.erase a₀) (Finset.erase_ssubset ha₀) hdist_erase hzero_erase
    intro a ha k hk
    rcases eq_or_ne a a₀ with rfl | hane
    · exact hda₀ k hk
    · exact hrest a (Finset.mem_erase.mpr ⟨hane, ha⟩) k hk

/-- **Abstract exp/log fibre rigidity.**  For a real clock `L` that is unbounded along a sequence in
every infinite fibre, the shift factors `exp(-α a · L)` and clock `L` satisfy
`FactorClockFiberIndependent` at every jet order, provided the shift real parts are distinct. -/
theorem factorClockFiberIndependent_of_expLog
    {P : Type*} [Fintype A]
    (alpha : A → ℂ) (L : P → ℝ)
    (hdistinct : Function.Injective (fun a => (alpha a).re))
    (hLproper : ∀ V : Set P, V.Infinite →
      ∃ q : ℕ → P, (∀ n, q n ∈ V) ∧ Tendsto (fun n => L (q n)) atTop atTop)
    (m : ℕ) :
    FactorClockFiberIndependent
      (fun a p => Complex.exp (-(alpha a) * (L p : ℂ)))
      (fun p => (L p : ℂ)) m := by
  intro U hU D hbad
  set t : Set P :=
    {p | p ∈ U ∧ ∑ ak, D ak * Complex.exp (-(alpha ak.1) * (L p : ℂ)) * (L p : ℂ) ^ (ak.2 : ℕ) ≠ 0}
    with ht
  have hgood : (U \ t).Infinite := hU.diff hbad
  obtain ⟨q, hqmem, hqtend⟩ := hLproper (U \ t) hgood
  set u : ℕ → ℝ := fun n => L (q n) with hu_def
  have hu : Tendsto u atTop atTop := hqtend
  have hq0 : ∀ n, ∑ ak, D ak * Complex.exp (-(alpha ak.1) * (u n : ℂ))
      * (u n : ℂ) ^ (ak.2 : ℕ) = 0 := by
    intro n
    have hmem := hqmem n
    rw [Set.mem_diff] at hmem
    obtain ⟨hqU, hqnt⟩ := hmem
    by_contra hne
    exact hqnt ⟨hqU, hne⟩
  -- coefficient function in `ℕ`-index form
  set dR : A → ℕ → ℂ := fun a k => if h : k < m + 1 then D (a, ⟨k, h⟩) else 0 with hdR
  have hDR : ∀ a (j : Fin (m + 1)), dR a (j : ℕ) = D (a, j) := by
    intro a j
    simp only [hdR, j.isLt, dif_pos]
  have hzero : ∀ n, ∑ a : A, (∑ k ∈ Finset.range (m + 1), dR a k * (u n : ℂ) ^ k)
      * Complex.exp (-(alpha a) * (u n : ℂ)) = 0 := by
    intro n
    have hregroup : (∑ ak, D ak * Complex.exp (-(alpha ak.1) * (u n : ℂ)) * (u n : ℂ) ^ (ak.2 : ℕ))
        = ∑ a : A, (∑ k ∈ Finset.range (m + 1), dR a k * (u n : ℂ) ^ k)
            * Complex.exp (-(alpha a) * (u n : ℂ)) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      dsimp only
      have hinner : (∑ y : Fin (m + 1), D (a, y) * (u n : ℂ) ^ (y : ℕ))
          = ∑ k ∈ Finset.range (m + 1), dR a k * (u n : ℂ) ^ k := by
        rw [← Fin.sum_univ_eq_sum_range (fun k => dR a k * (u n : ℂ) ^ k) (m + 1)]
        apply Finset.sum_congr rfl
        intro k _
        rw [hDR a k]
      rw [← hinner, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      ring
    rw [← hregroup, hq0 n]
  have hdist_univ : ∀ a ∈ (Finset.univ : Finset A), ∀ b ∈ (Finset.univ : Finset A),
      (alpha a).re = (alpha b).re → a = b := fun a _ b _ h => hdistinct h
  have hcoef := expPoly_rigidity m alpha dR u hu Finset.univ hdist_univ hzero
  funext ak
  obtain ⟨a, j⟩ := ak
  have hj : dR a (j : ℕ) = 0 := hcoef a (Finset.mem_univ a) (j : ℕ) j.isLt
  rw [hDR a j] at hj
  simpa using hj

/-- The prime logarithmic clock `p ↦ log p`, valued in `ℂ`. -/
def primeLogClock (p : Nat.Primes) : ℂ := (Real.log (p : ℕ) : ℂ)

/-- The prime-Dirichlet shift factor `p ↦ p^{-α} = exp(-α · log p)`. -/
def primeShiftFactor (α : ℂ) (p : Nat.Primes) : ℂ := Complex.exp (-α * primeLogClock p)

theorem primeShiftFactor_ne_zero (α : ℂ) (p : Nat.Primes) : primeShiftFactor α p ≠ 0 :=
  Complex.exp_ne_zero _

/-- The prime logarithm is unbounded along a sequence inside every infinite set of primes: an
infinite set of primes is unbounded in `ℕ`, and `log` is monotone to `+∞`. -/
theorem primeLog_proper (V : Set Nat.Primes) (hV : V.Infinite) :
    ∃ q : ℕ → Nat.Primes, (∀ n, q n ∈ V) ∧
      Tendsto (fun n => Real.log (q n : ℕ)) atTop atTop := by
  have hunb : ∀ N : ℕ, ∃ p ∈ V, N < (p : ℕ) := by
    intro N
    by_contra hcon
    have hle : ∀ p ∈ V, (p : ℕ) ≤ N := by
      intro p hp
      by_contra hlt
      exact hcon ⟨p, hp, not_le.mp hlt⟩
    have hsub : V ⊆ (Subtype.val ⁻¹' Set.Iic N) := fun p hp => hle p hp
    exact hV (Set.Finite.subset
      ((Set.finite_Iic N).preimage (Subtype.val_injective.injOn)) hsub)
  choose q hqV hqlt using hunb
  refine ⟨q, hqV, ?_⟩
  have hcast : Tendsto (fun n => ((q n : ℕ) : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    exact_mod_cast le_of_lt (hqlt n)
  simpa [Function.comp] using Real.tendsto_log_atTop.comp hcast

/-- **Prime exponential-polynomial fibre rigidity — acceptance theorem.**  For the genuine prime
columns `factor a p = p^{-α a}` and clock `p ↦ log p`, with the finite shifts of pairwise distinct
real part, `FactorClockFiberIndependent` holds at every jet order, with no rigidity hypothesis. -/
theorem primeFactorClockFiberIndependent
    [Fintype A] (alpha : A → ℂ) (hdistinct : Function.Injective (fun a => (alpha a).re)) (m : ℕ) :
    FactorClockFiberIndependent (fun a p => primeShiftFactor (alpha a) p) primeLogClock m :=
  factorClockFiberIndependent_of_expLog alpha (fun p : Nat.Primes => Real.log (p : ℕ))
    hdistinct primeLog_proper m

omit [DecidableEq A] in
/-- A finite prime shift palette has a nowhere-zero factor: the exponential factor never vanishes. -/
theorem primeShiftFactor_hasNowhereZeroFactor [Nonempty A] (alpha : A → ℂ) :
    HasNowhereZeroFactor (fun a (p : Nat.Primes) => primeShiftFactor (alpha a) p) :=
  ⟨Classical.arbitrary A, fun p => primeShiftFactor_ne_zero _ p⟩

/-- **Prime finite-range collapse with rigidity discharged.**  For a finite-range prime coefficient
family and a finite shift palette of pairwise distinct real parts, the complete operator-tail
condition collapses exactly to scalar tail independence — with the classical fibre rigidity supplied
internally rather than assumed. -/
theorem primeCompleteShiftJetTailIndependent_iff
    {J : Type*} [Fintype J] [Fintype A] [Nonempty A]
    (c : J → Nat.Primes → ℂ) (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a => (alpha a).re))
    (hrange : (Set.range (coefficientPattern c)).Finite) :
    CompleteShiftJetTailIndependent c (fun a p => primeShiftFactor (alpha a) p) primeLogClock
      ↔ TailCoefficientIndependent c :=
  completeShiftJetTailIndependent_iff_of_finiteRange c
    (fun a p => primeShiftFactor (alpha a) p) primeLogClock hrange
    (primeShiftFactor_hasNowhereZeroFactor alpha)
    (fun m => primeFactorClockFiberIndependent alpha hdistinct m)

end

end GaloisForLFunctions.HTGeometry
