import GaloisForLFunctions.RHTower.BeurlingSystemDecomposition

/-!
# The zeta series of a Beurling system

Linear counting makes the generalized-integer Dirichlet series converge on the half-plane to the
right of one.  Grouping the generalized integers into dyadic norm blocks turns the series into a
geometric series with ratio `2^{1-s}`: the block `2^k < |g| ≤ 2^{k+1}` carries at most `N(2^{k+1})`
integers, each of weight at most `2^{-ks}`.
-/

open scoped BigOperators

namespace RHTower

namespace BeurlingSystem

variable (B : BeurlingSystem)

/-- The dyadic block index of a generalized integer. -/
noncomputable def dyadicIndex (g : Multiset B.Label) : ℕ := ⌊Real.logb 2 (B.intNorm g)⌋₊

variable {B}

theorem two_pow_dyadicIndex_le (g : Multiset B.Label) :
    (2 : ℝ) ^ (B.dyadicIndex g) ≤ B.intNorm g := by
  have hpos : 0 < B.intNorm g := B.intNorm_pos g
  have hone : 1 ≤ B.intNorm g := B.one_le_intNorm g
  have hlogb : 0 ≤ Real.logb 2 (B.intNorm g) :=
    Real.logb_nonneg (by norm_num) hone
  have hfloor : ((B.dyadicIndex g : ℕ) : ℝ) ≤ Real.logb 2 (B.intNorm g) :=
    Nat.floor_le hlogb
  have hpow : (2 : ℝ) ^ ((B.dyadicIndex g : ℕ) : ℝ) ≤ (2 : ℝ) ^ (Real.logb 2 (B.intNorm g)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor
  rwa [Real.rpow_logb (by norm_num) (by norm_num) hpos, Real.rpow_natCast] at hpow

theorem intNorm_lt_two_pow_succ (g : Multiset B.Label) :
    B.intNorm g < (2 : ℝ) ^ (B.dyadicIndex g + 1) := by
  have hpos : 0 < B.intNorm g := B.intNorm_pos g
  have hlt : Real.logb 2 (B.intNorm g) < ((B.dyadicIndex g : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hpow : (2 : ℝ) ^ (Real.logb 2 (B.intNorm g))
      < (2 : ℝ) ^ (((B.dyadicIndex g : ℕ) : ℝ) + 1) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
  rw [Real.rpow_logb (by norm_num) (by norm_num) hpos] at hpow
  have hcast : (2 : ℝ) ^ (((B.dyadicIndex g : ℕ) : ℝ) + 1) = (2 : ℝ) ^ (B.dyadicIndex g + 1) := by
    rw [show (((B.dyadicIndex g : ℕ) : ℝ) + 1) = ((B.dyadicIndex g + 1 : ℕ) : ℝ) from by push_cast; ring,
      Real.rpow_natCast]
  rwa [hcast] at hpow

/-- **Convergence of the zeta series.**  Linear counting gives absolute convergence of
`∑_g |g|^{-s}` for every real `s > 1`. -/
theorem summable_intNorm_rpow (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    {s : ℝ} (hs : 1 < s) :
    Summable fun g : Multiset B.Label => (B.intNorm g) ^ (-s) := by
  classical
  have hC0 : 0 ≤ C := by
    have h1 := hC 1 le_rfl
    have h2 : (0 : ℝ) ≤ (B.countBall 1 : ℝ) := Nat.cast_nonneg _
    linarith
  set r : ℝ := (2 : ℝ) ^ (1 - s) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    rw [hr]
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeom : Summable fun k : ℕ => 2 * C * r ^ k :=
    (summable_geometric_of_lt_one hr0.le hr1).mul_left _
  set K : ℝ := ∑' k : ℕ, 2 * C * r ^ k with hK
  refine summable_of_sum_le (c := K) (fun g => Real.rpow_nonneg (B.intNorm_pos g).le _) fun S => ?_
  have hmaps : ∀ g ∈ S, B.dyadicIndex g ∈ S.image B.dyadicIndex :=
    fun g hg => Finset.mem_image_of_mem _ hg
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hblock : ∀ k ∈ S.image B.dyadicIndex,
      ∑ g ∈ S with B.dyadicIndex g = k, (B.intNorm g) ^ (-s) ≤ 2 * C * r ^ k := by
    intro k _
    have hterm : ∀ g ∈ S.filter fun g => B.dyadicIndex g = k,
        (B.intNorm g) ^ (-s) ≤ ((2 : ℝ) ^ k) ^ (-s) := by
      intro g hg
      have hgk : B.dyadicIndex g = k := (Finset.mem_filter.mp hg).2
      have hle : (2 : ℝ) ^ k ≤ B.intNorm g := by
        rw [← hgk]
        exact two_pow_dyadicIndex_le g
      have hpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      exact Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
    have hfin := hdisc ((2 : ℝ) ^ (k + 1))
    have hcards : (S.filter fun g => B.dyadicIndex g = k).card ≤ B.countBall ((2 : ℝ) ^ (k + 1)) := by
      rw [countBall, Set.ncard_eq_toFinset_card _ hfin]
      refine Finset.card_le_card fun g hg => ?_
      rw [Set.Finite.mem_toFinset]
      rw [Finset.mem_filter] at hg
      have hgk : B.dyadicIndex g = k := hg.2
      have hlt := intNorm_lt_two_pow_succ g
      rw [hgk] at hlt
      exact hlt.le
    have hcount : ((S.filter fun g => B.dyadicIndex g = k).card : ℝ) ≤ C * (2 : ℝ) ^ (k + 1) := by
      have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
      calc ((S.filter fun g => B.dyadicIndex g = k).card : ℝ)
          ≤ (B.countBall ((2 : ℝ) ^ (k + 1)) : ℝ) := by exact_mod_cast hcards
        _ ≤ C * (2 : ℝ) ^ (k + 1) := hC _ hone
    have hweight : ((2 : ℝ) ^ k) ^ (-s) = ((2 : ℝ) ^ (-s)) ^ k := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (-s)) k, ← Real.rpow_natCast (2 : ℝ) k,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    calc ∑ g ∈ S with B.dyadicIndex g = k, (B.intNorm g) ^ (-s)
        ≤ ∑ g ∈ S with B.dyadicIndex g = k, ((2 : ℝ) ^ k) ^ (-s) := Finset.sum_le_sum hterm
      _ = ((S.filter fun g => B.dyadicIndex g = k).card : ℝ) * ((2 : ℝ) ^ k) ^ (-s) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C * (2 : ℝ) ^ (k + 1)) * ((2 : ℝ) ^ k) ^ (-s) := by
          refine mul_le_mul_of_nonneg_right hcount ?_
          positivity
      _ = 2 * C * r ^ k := by
          rw [hweight, hr, pow_succ]
          have h2 : (2 : ℝ) ^ (1 - s) = (2 : ℝ) ^ (-s) * (2 : ℝ) := by
            rw [show (1 : ℝ) - s = (-s) + 1 from by ring, Real.rpow_add (by norm_num),
              Real.rpow_one]
          rw [h2, mul_pow]
          ring
  calc ∑ k ∈ S.image B.dyadicIndex, ∑ g ∈ S with B.dyadicIndex g = k, (B.intNorm g) ^ (-s)
      ≤ ∑ k ∈ S.image B.dyadicIndex, 2 * C * r ^ k := Finset.sum_le_sum hblock
    _ ≤ K := by
        refine hgeom.sum_le_tsum _ fun k _ => ?_
        have : (0 : ℝ) ≤ r ^ k := (pow_pos hr0 k).le
        positivity


/-! ## The zeta and Möbius Dirichlet series -/

variable (B) in
/-- The zeta series of a Beurling system. -/
noncomputable def zetaSeries (s : ℝ) : ℝ := ∑' g : Multiset B.Label, (B.intNorm g) ^ (-s)

variable (B) in
/-- The generalized Möbius Dirichlet series. -/
noncomputable def moebiusSeries (s : ℝ) : ℝ :=
  ∑' g : Multiset B.Label, (B.moebius g : ℝ) * (B.intNorm g) ^ (-s)

theorem summable_moebiusTerm (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    {s : ℝ} (hs : 1 < s) :
    Summable fun g : Multiset B.Label => (B.moebius g : ℝ) * (B.intNorm g) ^ (-s) := by
  refine Summable.of_norm_bounded (summable_intNorm_rpow hdisc hC hs) fun g => ?_
  have hnn : (0 : ℝ) ≤ (B.intNorm g) ^ (-s) := Real.rpow_nonneg (B.intNorm_pos g).le _
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn]
  have h1 := abs_moebius_le_one (B := B) g
  nlinarith

theorem zetaSeries_pos (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    {s : ℝ} (hs : 1 < s) : 0 < B.zetaSeries s := by
  have hsum := summable_intNorm_rpow hdisc hC hs
  have hterm : ∀ g : Multiset B.Label, 0 ≤ (B.intNorm g) ^ (-s) :=
    fun g => Real.rpow_nonneg (B.intNorm_pos g).le _
  have hone : (0 : ℝ) < (B.intNorm (0 : Multiset B.Label)) ^ (-s) := by
    rw [intNorm_zero, Real.one_rpow]
    norm_num
  rw [zetaSeries]
  exact lt_of_lt_of_le hone (hsum.le_tsum 0 fun g _ => hterm g)


/-! ## Dirichlet inversion -/

open scoped Classical in
/-- The ordered factorizations of a generalized integer are its divisors. -/
noncomputable def divisorPairEquiv [DecidableEq B.Label] (n : Multiset B.Label) :
    {p : (Multiset B.Label) × (Multiset B.Label) // p.1 + p.2 = n} ≃ ↥(n.powerset.toFinset) where
  toFun p := ⟨p.1.1, by
    rw [Multiset.mem_toFinset, Multiset.mem_powerset]
    exact Multiset.le_iff_exists_add.mpr ⟨p.1.2, p.2.symm⟩⟩
  invFun d := ⟨(d.1, n - d.1), by
    have hd : d.1 ≤ n := by
      have hmem := d.2
      rw [Multiset.mem_toFinset, Multiset.mem_powerset] at hmem
      exact hmem
    exact add_tsub_cancel_of_le hd⟩
  left_inv := by
    rintro ⟨⟨d, e⟩, hde⟩
    apply Subtype.ext
    have he : n - d = e := by
      rw [← hde, add_tsub_cancel_left]
    simp [he]
  right_inv := by
    rintro ⟨d, hd⟩
    rfl

/-- **The Dirichlet inversion.**  The generalized Möbius series is the reciprocal of the zeta
series on the half-plane of absolute convergence. -/
theorem moebiusSeries_mul_zetaSeries (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    {s : ℝ} (hs : 1 < s) : B.moebiusSeries s * B.zetaSeries s = 1 := by
  classical
  set F : (Multiset B.Label) × (Multiset B.Label) → ℝ := fun p =>
    ((B.moebius p.1 : ℝ) * (B.intNorm p.1) ^ (-s)) * ((B.intNorm p.2) ^ (-s)) with hF
  have hZ := summable_intNorm_rpow hdisc hC hs
  have hM := summable_moebiusTerm hdisc hC hs
  have hprod : Summable fun p : (Multiset B.Label) × (Multiset B.Label) =>
      (B.intNorm p.1) ^ (-s) * (B.intNorm p.2) ^ (-s) :=
    hZ.mul_of_nonneg hZ (fun g => Real.rpow_nonneg (B.intNorm_pos g).le _)
      (fun g => Real.rpow_nonneg (B.intNorm_pos g).le _)
  have hFsum : Summable F := by
    refine hprod.of_norm_bounded fun p => ?_
    have hnn1 : (0 : ℝ) ≤ (B.intNorm p.1) ^ (-s) := Real.rpow_nonneg (B.intNorm_pos _).le _
    have hnn2 : (0 : ℝ) ≤ (B.intNorm p.2) ^ (-s) := Real.rpow_nonneg (B.intNorm_pos _).le _
    have h1 := abs_moebius_le_one (B := B) p.1
    rw [hF]
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hnn1, abs_of_nonneg hnn2]
    calc |(B.moebius p.1 : ℝ)| * (B.intNorm p.1) ^ (-s) * (B.intNorm p.2) ^ (-s)
        ≤ 1 * (B.intNorm p.1) ^ (-s) * (B.intNorm p.2) ^ (-s) := by gcongr
      _ = (B.intNorm p.1) ^ (-s) * (B.intNorm p.2) ^ (-s) := by ring
  have hpairsum : B.moebiusSeries s * B.zetaSeries s = ∑' p, F p := by
    rw [moebiusSeries, zetaSeries, hF]
    exact hM.tsum_mul_tsum hZ hFsum
  rw [hpairsum]
  -- regroup by the product
  set e := Equiv.sigmaFiberEquiv fun p : (Multiset B.Label) × (Multiset B.Label) => p.1 + p.2
    with he
  have hsigma : Summable (F ∘ e) := (e.summable_iff).mpr hFsum
  have hregroup : ∑' p, F p = ∑' n : Multiset B.Label,
      ∑' c : {p : (Multiset B.Label) × (Multiset B.Label) // p.1 + p.2 = n}, F (c : _ × _) := by
    have h1 : ∑' p, F p
        = ∑' x : (Σ n : Multiset B.Label,
            {p : (Multiset B.Label) × (Multiset B.Label) // p.1 + p.2 = n}), (F ∘ e) x :=
      (e.tsum_eq F).symm
    rw [h1, hsigma.tsum_sigma]
    rfl
  rw [hregroup]
  have hfibre : ∀ n : Multiset B.Label,
      (∑' c : {p : (Multiset B.Label) × (Multiset B.Label) // p.1 + p.2 = n}, F (c : _ × _))
        = (if n = 0 then (1 : ℝ) else 0) := by
    intro n
    letI : Fintype {p : (Multiset B.Label) × (Multiset B.Label) // p.1 + p.2 = n} :=
      Fintype.ofEquiv _ (divisorPairEquiv n).symm
    rw [tsum_fintype]
    have hval : ∀ c : {p : (Multiset B.Label) × (Multiset B.Label) // p.1 + p.2 = n},
        F (c : (Multiset B.Label) × (Multiset B.Label))
          = (B.moebius ((c : (Multiset B.Label) × (Multiset B.Label)).1) : ℝ)
            * (B.intNorm n) ^ (-s) := by
      rintro ⟨⟨d, g⟩, hdg⟩
      have hnorm : B.intNorm d * B.intNorm g = B.intNorm n := by
        rw [← intNorm_add, hdg]
      rw [hF]
      simp only
      rw [mul_assoc, ← Real.mul_rpow (B.intNorm_pos d).le (B.intNorm_pos g).le, hnorm]
    rw [Finset.sum_congr rfl fun c _ => hval c, ← Finset.sum_mul]
    have hsum : ∑ c : {p : (Multiset B.Label) × (Multiset B.Label) // p.1 + p.2 = n},
        (B.moebius ((c : (Multiset B.Label) × (Multiset B.Label)).1) : ℝ)
        = ((∑ d ∈ n.powerset.toFinset, B.moebius d : ℤ) : ℝ) := by
      push_cast
      rw [← Finset.sum_coe_sort n.powerset.toFinset (fun d => (B.moebius d : ℝ))]
      refine Fintype.sum_equiv (divisorPairEquiv n)
        (fun c => (B.moebius ((c : (Multiset B.Label) × (Multiset B.Label)).1) : ℝ))
        (fun d => (B.moebius (d : Multiset B.Label) : ℝ)) ?_
      intro c
      rfl
    rw [hsum, B.sum_moebius_divisors n]
    by_cases hn : n = 0
    · rw [if_pos hn, if_pos hn, hn, intNorm_zero, Real.one_rpow]
      norm_num
    · rw [if_neg hn, if_neg hn]
      norm_num
  rw [tsum_congr hfibre, tsum_eq_single 0]
  · rw [if_pos rfl]
  · intro n hn
    rw [if_neg hn]

end BeurlingSystem

end RHTower
