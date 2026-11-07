import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormMoments
import GaloisForLFunctions.ArtinMertens.TheMertensConstantsInProgressionsExist
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Charges beyond the gcd profiles are coercive

An `M`-periodic twist `F` that is not a function of `gcd(·, M)` has some `n₀` with
`δ = F(n₀) − F(d) ≠ 0`, `d = gcd(n₀, M)`. With `q = M/d` and `r = n₀/d` (a unit mod `q`), every
`k ≡ r (mod q)` maps the progression `d + Mℕ` into the class of `n₀`, so the primes of that class move
`F` by `δ` on a progression of harmonic mass `≈ log N/M` (`exists_moving_class`,
`jumpEnergy_ge_of_progression`). Mertens' theorem in progressions gives the class the mass
`log x/(2φ(q))` past a threshold depending on `q`, hence

`J_N(F) ≥ η² (log N)² / (16 M²)`,  `η ≤ |F(n₀) − F(gcd(n₀, M))|`,

uniformly over every period `M` up to the admissible scale `M₀(N)` (`jumpEnergy_ge_beyond_gcd`). The
scale `M₀(N)` is the largest `Q ≤ log log N` whose moduli are all past their Mertens thresholds at
`√N`; it tends to infinity (`tendsto_admissiblePeriod_atTop`).

The neutral unit-normalized charge `u = (F − λ)/√log N` has `‖u‖² ≤ 8V²` and
`J(u) ≥ η² log N/(16M²)`, while the complete form differs from the jump energy by
`O(V²(c² + c³))` (`exists_complete_packet_two_moment_bound`). Along `c ≤ (log N)^{1/4}`, which contains
the critical curve `c⁸ = R log N` at every ratio `R`:

* `W(u) ≥ (1 − ε) J(u)` (`eventually_completeWeilEnergy_ge_beyond_gcd`);
* `W(u) ≥ η² log N / (256 V² (log log N)²) · ‖u‖²` (`eventually_completeWeilEnergy_coercive_beyond_gcd`).

So periodic charges of growing period outside the gcd profiles carry no nonpositive direction at any
critical ratio; only the gcd profiles, which lie in the conductor subspace, remain.
-/

noncomputable section
set_option autoImplicit false

open Finset Filter Topology ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticCouplingTheory

open RenormalizedArithmeticPotentialTheory CompletedArithmeticForms

/-! ### The jump energy along a moving progression -/

private theorem sum_inv_eq_harmonic_real (N : ℕ) :
    ∑ n ∈ Icc 1 N, 1 / (n : ℝ) = ((harmonic N : ℚ) : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp only [one_div]

/-- **Jump energy along a progression.** If every `k ∈ P ⊆ [1, X]` moves `F` by `δ` along
`d + Mℕ`, then `J_N(F) ≥ (δ²/M) (Σ_{k ∈ P} Λ(k)/k) (log N − log(XM))`. -/
theorem jumpEnergy_ge_of_progression {M d X : ℕ} (hM : 0 < M) (hd : 1 ≤ d) (hdM : d ≤ M)
    (hX : 0 < X) {F : ℕ → ℝ} {δ : ℝ} {P : Finset ℕ} (hP : ∀ k ∈ P, 1 ≤ k ∧ k ≤ X)
    (hmove : ∀ k ∈ P, ∀ j : ℕ, F (k * (d + M * j)) - F (d + M * j) = δ) {N : ℕ} (hN : 1 ≤ N) :
    δ ^ 2 / M * ((∑ k ∈ P, Λ k / k) * (Real.log N - Real.log ((X * M : ℕ) : ℝ))) ≤
      jumpEnergy N F := by
  classical
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨Y, hY⟩ : ∃ Y, Y = N / (X * M) := ⟨_, rfl⟩
  have hXM : 0 < X * M := Nat.mul_pos hX hM
  obtain ⟨m, hm⟩ : ∃ m : ℕ → ℕ, m = fun i => d + M * (i - 1) := ⟨_, rfl⟩
  have hmle : ∀ i ∈ Icc 1 Y, m i ≤ M * i := fun i hi => by
    have hi1 := (mem_Icc.mp hi).1
    rw [hm]
    dsimp only
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [Nat.add_sub_cancel, mul_add, mul_one]
    omega
  have hm1 : ∀ i, 1 ≤ m i := fun i => by
    rw [hm]
    dsimp only
    omega
  have hmYX : ∀ i ∈ Icc 1 Y, ∀ k ∈ P, k * m i ≤ N := fun i hi k hk => by
    have hkX : k ≤ X := (hP k hk).2
    have hiY := (mem_Icc.mp hi).2
    calc
      k * m i ≤ X * (M * Y) := Nat.mul_le_mul hkX ((hmle i hi).trans (Nat.mul_le_mul_left M hiY))
      _ = (X * M) * Y := by ring
      _ ≤ N := by rw [hY]; exact Nat.mul_div_le N (X * M)
  have hminj : Set.InjOn m (Icc 1 Y : Finset ℕ) := fun i hi j hj hij => by
    have hi1 := (mem_Icc.mp (mem_coe.mp hi)).1
    have hj1 := (mem_Icc.mp (mem_coe.mp hj)).1
    rw [hm] at hij
    dsimp only at hij
    have h := Nat.eq_of_mul_eq_mul_left hM (Nat.add_left_cancel hij)
    omega
  have hjump : ∀ k ∈ P, ∀ i, F (k * m i) - F (m i) = δ := fun k hk i => by
    rw [hm]
    exact hmove k hk (i - 1)
  have hnn : ∀ p : ℕ × ℕ, 0 ≤ Λ p.1 / p.1 * ((F (p.1 * p.2) - F p.2) ^ 2 / p.2) := fun p =>
    mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
      (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have hΛ0 : ∀ k : ℕ, 0 ≤ Λ k / k := fun k => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)
  -- restrict the energy to the family
  have hrestrict : ∑ k ∈ P, ∑ i ∈ Icc 1 Y, Λ k / k * (δ ^ 2 / (m i : ℝ)) ≤ jumpEnergy N F := by
    unfold jumpEnergy
    have himage : ∑ k ∈ P, ∑ i ∈ Icc 1 Y, Λ k / k * (δ ^ 2 / (m i : ℝ)) =
        ∑ p ∈ P ×ˢ ((Icc 1 Y).image m), Λ p.1 / p.1 * ((F (p.1 * p.2) - F p.2) ^ 2 / p.2) := by
      rw [sum_product]
      refine sum_congr rfl fun k hk => ?_
      rw [sum_image hminj]
      refine sum_congr rfl fun i _ => ?_
      simp only
      rw [hjump k hk i]
    rw [himage]
    refine sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => hnn p
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_product.mp hp
    obtain ⟨i, hi, hpi⟩ := mem_image.mp hp2
    have hprod : p.1 * p.2 ≤ N := hpi ▸ hmYX i hi p.1 hp1
    have hk1 := (hP p.1 hp1).1
    have hm1i : 1 ≤ p.2 := hpi ▸ hm1 i
    exact mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_Icc.mpr ⟨hk1, (Nat.le_mul_of_pos_right _ hm1i).trans hprod⟩,
        mem_Icc.mpr ⟨hm1i, (Nat.le_mul_of_pos_left _ hk1).trans hprod⟩⟩, hprod⟩
  -- the harmonic mass of the progression
  have hlogY : Real.log N - Real.log ((X * M : ℕ) : ℝ) ≤ ∑ i ∈ Icc 1 Y, 1 / (i : ℝ) := by
    have hlt : N < (X * M) * (Y + 1) := by rw [hY]; exact Nat.lt_mul_div_succ N hXM
    have hltR : (N : ℝ) ≤ ((X * M : ℕ) : ℝ) * ((Y + 1 : ℕ) : ℝ) := by
      exact_mod_cast hlt.le
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hXM0 : (0 : ℝ) < ((X * M : ℕ) : ℝ) := by exact_mod_cast hXM
    have hY0 : (0 : ℝ) < ((Y + 1 : ℕ) : ℝ) := by positivity
    have hl := Real.log_le_log hN0 hltR
    rw [Real.log_mul hXM0.ne' hY0.ne'] at hl
    rw [sum_inv_eq_harmonic_real]
    have hh := log_add_one_le_harmonic Y
    linarith only [hl, hh]
  have hharm0 : 0 ≤ ∑ i ∈ Icc 1 Y, 1 / (i : ℝ) := sum_nonneg fun i _ => by positivity
  have hbound : δ ^ 2 / M * ((∑ k ∈ P, Λ k / k) * ∑ i ∈ Icc 1 Y, 1 / (i : ℝ)) ≤
      ∑ k ∈ P, ∑ i ∈ Icc 1 Y, Λ k / k * (δ ^ 2 / (m i : ℝ)) := by
    rw [sum_mul_sum, mul_sum]
    refine sum_le_sum fun k _ => ?_
    rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (mem_Icc.mp hi).1
    have hmi : (m i : ℝ) ≤ M * i := by exact_mod_cast hmle i hi
    have hmi0 : (0 : ℝ) < m i := by exact_mod_cast hm1 i
    have hfrac : δ ^ 2 / (M * i) ≤ δ ^ 2 / (m i : ℝ) :=
      div_le_div_of_nonneg_left (sq_nonneg δ) hmi0 hmi
    have h := mul_le_mul_of_nonneg_left hfrac (hΛ0 k)
    refine le_trans (le_of_eq ?_) h
    have hi0 : (i : ℝ) ≠ 0 := by positivity
    field_simp
  have hmass0 : 0 ≤ ∑ k ∈ P, Λ k / k := sum_nonneg fun k _ => hΛ0 k
  refine le_trans ?_ (hbound.trans hrestrict)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  by_cases hsign : Real.log N - Real.log ((X * M : ℕ) : ℝ) ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos hmass0 hsign).trans (mul_nonneg hmass0 hharm0)
  · exact mul_le_mul_of_nonneg_left hlogY hmass0

/-- **The moving class.** With `d = gcd(n₀, M)`, `q = M/d`, `r = n₀/d`: `r` is a unit mod `q`, and
every `k ≡ r (mod q)` maps `d + Mℕ` into the class of `n₀`. -/
theorem exists_moving_class {M : ℕ} (hM : 0 < M) {F : ℕ → ℝ} (hper : Function.Periodic F M)
    (n₀ : ℕ) :
    ∃ d q r : ℕ, 1 ≤ d ∧ d ≤ M ∧ 0 < q ∧ q ≤ M ∧ r.Coprime q ∧
      ∀ k : ℕ, (k : ZMod q) = (r : ZMod q) → ∀ j : ℕ,
        F (k * (d + M * j)) - F (d + M * j) = F n₀ - F (n₀.gcd M) := by
  obtain ⟨d, hd⟩ : ∃ d, d = n₀.gcd M := ⟨_, rfl⟩
  have hdpos : 0 < d := by rw [hd]; exact Nat.gcd_pos_of_pos_right _ hM
  have hdM : d ≤ M := by rw [hd]; exact Nat.gcd_le_right _ hM
  obtain ⟨q, hq⟩ : ∃ q, q = M / d := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = n₀ / d := ⟨_, rfl⟩
  have hqd : q * d = M := by
    rw [hq]
    exact Nat.div_mul_cancel (by rw [hd]; exact Nat.gcd_dvd_right _ _)
  have hrd : r * d = n₀ := by
    rw [hr]
    exact Nat.div_mul_cancel (by rw [hd]; exact Nat.gcd_dvd_left _ _)
  have hcop : r.Coprime q := by
    rw [hr, hq, hd]
    exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ hM)
  have hq0 : 0 < q := by
    rw [hq]
    exact Nat.div_pos hdM hdpos
  have hqM : q ≤ M := by rw [hq]; exact Nat.div_le_self M d
  refine ⟨d, q, r, hdpos, hdM, hq0, hqM, hcop, fun k hk j => ?_⟩
  have hmF : F (d + M * j) = F (n₀.gcd M) := by
    rw [← hper.map_mod_nat (d + M * j), Nat.add_mul_mod_self_left, hper.map_mod_nat, hd]
  have hmod : k ≡ r [MOD q] := (ZMod.natCast_eq_natCast_iff k r q).mp hk
  have hmod2 : k * d ≡ r * d [MOD q * d] := hmod.mul_right' d
  rw [hqd, hrd] at hmod2
  have hkF : F (k * (d + M * j)) = F n₀ := by
    rw [← hper.map_mod_nat (k * (d + M * j)), ← hper.map_mod_nat n₀]
    have hexp : k * (d + M * j) = k * d + M * (k * j) := by ring
    rw [hexp, Nat.add_mul_mod_self_left]
    exact congrArg F hmod2
  rw [hkF, hmF]

/-! ### Mertens' theorem in progressions and the admissible period scale -/

/-- Mertens' theorem in progressions at half strength: past some `X₀`,
`Σ_{p ≤ x, p ≡ a (q)} log p/p ≥ log x/(2φ(q))` for every unit `a`. -/
theorem exists_mertens_progression_threshold (q : ℕ) [NeZero q] :
    ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x → ∀ a : ZMod q, IsUnit a →
      Real.log x / (2 * q.totient) ≤
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a),
          Real.log (p : ℝ) / (p : ℝ) := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hev : ∀ a : ZMod q, ∀ᶠ x : ℝ in atTop, IsUnit a → Real.log x / (2 * q.totient) ≤
      ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a),
        Real.log (p : ℝ) / (p : ℝ) := by
    intro a
    by_cases ha : IsUnit a
    · have ht := ArtinMertens.tendsto_sum_prime_log_div_residueClass_sub_log ha
      generalize (ArtinMertens.mertensConstantAP q a - ∑' n, ArtinMertens.classTail a n) = L at ht
      have h1 := ht.eventually (lt_mem_nhds (sub_one_lt L))
      have h2 := Real.tendsto_log_atTop.eventually_ge_atTop (2 * q.totient * (1 - L))
      filter_upwards [h1, h2] with x hx1 hx2 _
      have hy : Real.log x / q.totient = 2 * (Real.log x / (2 * q.totient)) := by
        field_simp
      have hy2 : 1 - L ≤ Real.log x / (2 * q.totient) := by
        rw [le_div_iff₀ (by positivity)]
        linarith only [hx2]
      linarith only [hx1, hy, hy2]
    · exact Eventually.of_forall fun _ h => absurd h ha
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (Filter.eventually_all.mpr hev)
  exact ⟨X₀, fun x hx a ha => hX₀ x hx a ha⟩

/-- A Mertens threshold of the progressions mod `q` (`0` for `q = 0`). -/
def mertensProgressionThreshold (q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    haveI : NeZero q := ⟨hq⟩
    Classical.choose (exists_mertens_progression_threshold q)

theorem mertensProgressionThreshold_spec {q : ℕ} (hq : 0 < q) {x : ℝ}
    (hx : mertensProgressionThreshold q ≤ x) (a : ZMod q) (ha : IsUnit a) :
    Real.log x / (2 * q.totient) ≤
      ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a),
        Real.log (p : ℝ) / (p : ℝ) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  unfold mertensProgressionThreshold at hx
  rw [dif_neg hq.ne'] at hx
  exact Classical.choose_spec (exists_mertens_progression_threshold q) x hx a ha

/-- The admissibility of a period scale `Q` at `N`: `Q ≤ log log N`, and every modulus `q ≤ Q`
is past its Mertens threshold at `√N`. -/
def admissiblePredicate (N Q : ℕ) : Prop :=
  (Q : ℝ) ≤ Real.log (Real.log N) ∧ ∀ q ∈ Finset.Icc 1 Q, mertensProgressionThreshold q ≤ Real.sqrt N

noncomputable instance (N : ℕ) : DecidablePred (admissiblePredicate N) := Classical.decPred _

/-- **The admissible period scale** `M₀(N)`: the largest admissible `Q ≤ N`. -/
def admissiblePeriod (N : ℕ) : ℕ := Nat.findGreatest (admissiblePredicate N) N

theorem admissiblePeriod_spec {N M : ℕ} (hM : 0 < M) (hMN : M ≤ admissiblePeriod N) :
    (M : ℝ) ≤ Real.log (Real.log N) ∧
      ∀ q ∈ Finset.Icc 1 M, mertensProgressionThreshold q ≤ Real.sqrt N := by
  have hne : admissiblePeriod N ≠ 0 := by omega
  have h : admissiblePredicate N (admissiblePeriod N) := Nat.findGreatest_of_ne_zero rfl hne
  obtain ⟨h1, h2⟩ := h
  refine ⟨le_trans (by exact_mod_cast hMN) h1, fun q hq => h2 q ?_⟩
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hq).1, (Finset.mem_Icc.mp hq).2.trans hMN⟩

/-- **The admissible period scale is unbounded.** -/
theorem tendsto_admissiblePeriod_atTop : Tendsto admissiblePeriod atTop atTop := by
  refine tendsto_atTop.mpr fun Q => ?_
  have hlog : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hthr : ∀ᶠ N : ℕ in atTop,
      ∀ q ∈ Finset.Icc 1 Q, mertensProgressionThreshold q ≤ Real.sqrt N := by
    refine (Filter.eventually_all_finset _).mpr fun q _ => ?_
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      (mertensProgressionThreshold q ^ 2)] with N hN
    exact (le_abs_self _).trans (Real.abs_le_sqrt hN)
  filter_upwards [eventually_ge_atTop Q, hlog.eventually_ge_atTop (Q : ℝ), hthr] with N hQN hQ hq
  exact Nat.le_findGreatest hQN (show admissiblePredicate N Q from ⟨hQ, hq⟩)

/-! ### The quantitative jump energy beyond the gcd profiles -/

/-- `log y ≤ y/4` for `y ≥ 9`. -/
theorem log_le_quarter {y : ℝ} (hy : 9 ≤ y) : Real.log y ≤ y / 4 := by
  have hy0 : 0 < y / 8 := by linarith
  have h1 : Real.log y = Real.log 8 + Real.log (y / 8) := by
    rw [← Real.log_mul (by norm_num) hy0.ne']
    congr 1
    ring
  have h2 := Real.log_le_sub_one_of_pos hy0
  have h3 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have h4 := Real.log_two_lt_d9
  linarith only [h1, h2, h3, h4, hy]

/-- **Outside the gcd profiles the jump energy is quadratic in `log N`**, uniformly for every
period up to the admissible scale. -/
theorem jumpEnergy_ge_beyond_gcd {N M : ℕ} (hM : 0 < M) (hMN : M ≤ admissiblePeriod N)
    (hL : 16 ≤ Real.log N) {F : ℕ → ℝ} (hper : Function.Periodic F M) {n₀ : ℕ} {η : ℝ}
    (hη0 : 0 ≤ η) (hη : η ≤ |F n₀ - F (n₀.gcd M)|) :
    η ^ 2 * Real.log N ^ 2 / (16 * M ^ 2) ≤ jumpEnergy N F := by
  obtain ⟨d, q, r, hd1, hdM, hq0, hqM, hcop, hmove⟩ := exists_moving_class hM hper n₀
  obtain ⟨hMlog, hthr⟩ := admissiblePeriod_spec hM hMN
  have hL0 : 0 < Real.log N := by linarith
  have hN1 : 1 ≤ N := by
    by_contra h
    have hN0 : N = 0 := by omega
    rw [hN0, Nat.cast_zero, Real.log_zero] at hL0
    exact lt_irrefl 0 hL0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set X := ⌊Real.sqrt N⌋₊ with hXdef
  have hsq1 : (1 : ℝ) ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN1)
  have hX : 0 < X := Nat.floor_pos.mpr hsq1
  set P := (Finset.Icc 1 X).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = (r : ZMod q)) with hPdef
  have hP : ∀ k ∈ P, 1 ≤ k ∧ k ≤ X := fun k hk => mem_Icc.mp (mem_filter.mp hk).1
  have hmoveP : ∀ k ∈ P, ∀ j : ℕ, F (k * (d + M * j)) - F (d + M * j) = F n₀ - F (n₀.gcd M) :=
    fun k hk j => hmove k (mem_filter.mp hk).2.2 j
  have hJ := jumpEnergy_ge_of_progression hM hd1 hdM hX hP hmoveP hN1
  -- the Mertens mass of the moving class up to `√N`
  haveI : NeZero q := ⟨hq0.ne'⟩
  have hunit : IsUnit (r : ZMod q) := (ZMod.isUnit_iff_coprime r q).mpr hcop
  have hmass := mertensProgressionThreshold_spec hq0 (hthr q (mem_Icc.mpr ⟨hq0, hqM⟩))
    (r : ZMod q) hunit
  rw [← hXdef, ← hPdef, Real.log_sqrt hN0.le] at hmass
  have hPΛ : ∑ k ∈ P, Λ k / k = ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ) :=
    sum_congr rfl fun k hk => by rw [vonMangoldt_apply_prime (mem_filter.mp hk).2.1]
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hφq : (q.totient : ℝ) ≤ M := by exact_mod_cast (Nat.totient_le q).trans hqM
  have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
  have hmassP : Real.log N / (4 * M) ≤ ∑ k ∈ P, Λ k / k := by
    rw [hPΛ]
    refine le_trans ?_ hmass
    rw [div_div, show (2 : ℝ) * (2 * (q.totient : ℝ)) = 4 * q.totient by ring]
    exact div_le_div_of_nonneg_left hL0.le (by positivity) (by linarith only [hφq])
  -- the length of the progression: `log N − log(XM) ≥ log N/4`
  have hXle : (X : ℝ) ≤ Real.sqrt N := Nat.floor_le (Real.sqrt_nonneg _)
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hlogXM : Real.log ((X * M : ℕ) : ℝ) ≤ Real.log N / 2 + Real.log M := by
    rw [Nat.cast_mul, Real.log_mul hX0.ne' hM0.ne', ← Real.log_sqrt hN0.le]
    linarith only [Real.log_le_log hX0 hXle]
  have hlogM : Real.log M ≤ Real.log N / 4 := by
    have hloglog : Real.log (Real.log N) ≤ Real.log N := Real.log_le_self hL0.le
    have h1 : Real.log M ≤ Real.log (Real.log N) :=
      Real.log_le_log hM0 (hMlog.trans hloglog)
    exact h1.trans (log_le_quarter (by linarith only [hL]))
  have hgap : Real.log N / 4 ≤ Real.log N - Real.log ((X * M : ℕ) : ℝ) := by
    linarith only [hlogXM, hlogM]
  -- assemble
  set δ := F n₀ - F (n₀.gcd M) with hδ
  have hδ2 : η ^ 2 ≤ δ ^ 2 := by
    have := pow_le_pow_left₀ hη0 hη 2
    rwa [sq_abs] at this
  have hmass0 : 0 ≤ Real.log N / (4 * M) := by positivity
  calc η ^ 2 * Real.log N ^ 2 / (16 * M ^ 2)
      = η ^ 2 / M * (Real.log N / (4 * M) * (Real.log N / 4)) := by
        field_simp
        ring
    _ ≤ δ ^ 2 / M * ((∑ k ∈ P, Λ k / k) * (Real.log N - Real.log ((X * M : ℕ) : ℝ))) := by
        refine mul_le_mul (div_le_div_of_nonneg_right hδ2 hM0.le)
          (mul_le_mul hmassP hgap (by positivity) (hmass0.trans hmassP)) (by positivity)
          (by positivity)
    _ ≤ jumpEnergy N F := hJ

/-! ### The neutral normalized charge -/

/-- The neutral shift `λ = (Σ_{n ≤ N} F(n)/n) / (Σ_{n ≤ N} 1/n)`. -/
def neutralShift (F : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Icc 1 N, F n / (n : ℝ)) / ∑ n ∈ Icc 1 N, 1 / (n : ℝ)

/-- The neutral unit-normalized charge `(F − λ)/√log N`. -/
def neutralCharge (F : ℕ → ℝ) (N n : ℕ) : ℝ :=
  (F n - neutralShift F N) / Real.sqrt (Real.log N)

theorem harmonic_mass_pos {N : ℕ} (hN : 1 ≤ N) : 0 < ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by
  have h1 : (1 : ℕ) ∈ Icc 1 N := mem_Icc.mpr ⟨le_rfl, hN⟩
  have h := single_le_sum (f := fun n : ℕ => 1 / (n : ℝ)) (fun n _ => by positivity) h1
  simp only [Nat.cast_one, div_one] at h
  linarith only [h]

theorem sum_neutralCharge_div {F : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, neutralCharge F N n / (n : ℝ) = 0 := by
  have hH := harmonic_mass_pos hN
  have hsplit : ∑ n ∈ Icc 1 N, neutralCharge F N n / (n : ℝ) =
      ((∑ n ∈ Icc 1 N, F n / (n : ℝ)) - neutralShift F N * ∑ n ∈ Icc 1 N, 1 / (n : ℝ)) /
        Real.sqrt (Real.log N) := by
    rw [mul_sum, ← sum_sub_distrib, sum_div]
    refine sum_congr rfl fun n _ => ?_
    unfold neutralCharge
    ring
  rw [hsplit]
  unfold neutralShift
  rw [div_mul_cancel₀ _ hH.ne', sub_self, zero_div]

theorem abs_neutralShift_le {F : ℕ → ℝ} {V : ℝ} (hV : ∀ n, |F n| ≤ V) {N : ℕ} (hN : 1 ≤ N) :
    |neutralShift F N| ≤ V := by
  have hH := harmonic_mass_pos hN
  unfold neutralShift
  rw [abs_div, abs_of_pos hH, div_le_iff₀ hH, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  rw [abs_div, abs_of_pos hn0, mul_one_div]
  exact div_le_div_of_nonneg_right (hV n) hn0.le

theorem jumpEnergy_neutralCharge (F : ℕ → ℝ) {N : ℕ} (hL : 0 < Real.log N) :
    jumpEnergy N (neutralCharge F N) = jumpEnergy N F / Real.log N := by
  have hs : Real.sqrt (Real.log N) ^ 2 = Real.log N := Real.sq_sqrt hL.le
  have key : ∀ a b : ℝ, ((a - neutralShift F N) / Real.sqrt (Real.log N) -
      (b - neutralShift F N) / Real.sqrt (Real.log N)) ^ 2 = (a - b) ^ 2 / Real.log N := by
    intro a b
    rw [div_sub_div_same, div_pow, hs]
    congr 1
    ring
  unfold jumpEnergy
  rw [sum_div]
  refine sum_congr rfl fun p _ => ?_
  unfold neutralCharge
  rw [key]
  ring

theorem norm_sq_packetVector_neutralCharge_le {F : ℕ → ℝ} {V : ℝ} (hV : ∀ n, |F n| ≤ V)
    {N : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ Real.log N) :
    ‖packetVector (neutralCharge F N) N‖ ^ 2 ≤ 8 * V ^ 2 := by
  have hL0 : 0 < Real.log N := by linarith
  have hlam := abs_neutralShift_le hV hN
  have hpt : ∀ n, neutralCharge F N n ^ 2 ≤ 4 * V ^ 2 / Real.log N := fun n => by
    unfold neutralCharge
    rw [div_pow, Real.sq_sqrt hL0.le]
    refine div_le_div_of_nonneg_right ?_ hL0.le
    have h1 := abs_le.mp (hV n)
    have h2 := abs_le.mp hlam
    nlinarith only [h1.1, h1.2, h2.1, h2.2]
  rw [packetVector_norm_sq]
  have hharm : ∑ n ∈ Icc 1 N, 1 / (n : ℝ) ≤ 1 + Real.log N := by
    rw [sum_inv_eq_harmonic_real]
    exact harmonic_le_one_add_log N
  calc ∑ n ∈ Icc 1 N, neutralCharge F N n ^ 2 / (n : ℝ)
      ≤ ∑ n ∈ Icc 1 N, 4 * V ^ 2 / Real.log N * (1 / (n : ℝ)) := by
        refine sum_le_sum fun n hn => ?_
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (hpt n) hn0.le
    _ = 4 * V ^ 2 / Real.log N * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by rw [mul_sum]
    _ ≤ 4 * V ^ 2 / Real.log N * (1 + Real.log N) :=
        mul_le_mul_of_nonneg_left hharm (by positivity)
    _ ≤ 8 * V ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hL0]
        nlinarith only [sq_nonneg V, hL]

theorem sum_sq_neutralCharge_le {F : ℕ → ℝ} {V : ℝ} (hV : ∀ n, |F n| ≤ V) {N : ℕ}
    (hN : 1 ≤ N) (hL : 0 < Real.log N) :
    ∑ n ∈ Icc 1 N, neutralCharge F N n ^ 2 ≤ 4 * V ^ 2 * N / Real.log N := by
  have hlam := abs_neutralShift_le hV hN
  have hpt : ∀ n, neutralCharge F N n ^ 2 ≤ 4 * V ^ 2 / Real.log N := fun n => by
    unfold neutralCharge
    rw [div_pow, Real.sq_sqrt hL.le]
    refine div_le_div_of_nonneg_right ?_ hL.le
    have h1 := abs_le.mp (hV n)
    have h2 := abs_le.mp hlam
    nlinarith only [h1.1, h1.2, h2.1, h2.2]
  calc ∑ n ∈ Icc 1 N, neutralCharge F N n ^ 2 ≤ ∑ _n ∈ Icc 1 N, 4 * V ^ 2 / Real.log N :=
        sum_le_sum fun n _ => hpt n
    _ = 4 * V ^ 2 * N / Real.log N := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp only [Nat.add_sub_cancel]
        ring

/-! ### The complete form beyond the gcd profiles -/

/-- The asymptotic inputs: `log N ≥ 16`, `(log N)^{1/4} ≤ N/3`, `K (log log N)² ≤ (log N)^{1/4}`. -/
theorem eventually_beyond_gcd_scales {K : ℝ} (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop, 16 ≤ Real.log N ∧ Real.log N ^ (1 / 4 : ℝ) ≤ (N : ℝ) / 3 ∧
      K * Real.log (Real.log N) ^ 2 ≤ Real.log N ^ (1 / 4 : ℝ) := by
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h2 := (Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 3)).natCast_atTop
  have h3 := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4)).bound
    (inv_pos.mpr hK)
  filter_upwards [hlogN.eventually_ge_atTop 16, h2, hlogN.eventually h3,
    eventually_ge_atTop 1] with N hL hN3 hK3 hN1
  have hL1 : 1 ≤ Real.log N := by linarith only [hL]
  have hL0 : 0 ≤ Real.log N := by linarith only [hL]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine ⟨hL, ?_, ?_⟩
  · have hle : Real.log N ^ (1 / 4 : ℝ) ≤ Real.log N := by
      calc Real.log N ^ (1 / 4 : ℝ) ≤ Real.log N ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
        _ = Real.log N := Real.rpow_one _
    rw [Real.norm_of_nonneg hL0, id, Real.norm_of_nonneg hN0] at hN3
    linarith only [hle, hN3]
  · have hll : 0 ≤ Real.log (Real.log N) := Real.log_nonneg hL1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hll _),
      Real.norm_of_nonneg (Real.rpow_nonneg hL0 _), Real.rpow_two] at hK3
    have := mul_le_mul_of_nonneg_left hK3 hK.le
    rwa [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul] at this

/-- **The complete form dominates the jump energy beyond the gcd profiles.** Eventually, for
`1 ≤ c ≤ (log N)^{1/4}`, every period `M ≤ M₀(N)` and every `M`-periodic `F` with `|F| ≤ V` and gcd
defect `|F(n₀) − F(gcd(n₀, M))| ≥ η`, the neutral charge `u` has `J(u) ≥ η² log N/(16M²)`,
`W(u) ≥ (1 − ε) J(u)` and `‖u‖² ≤ 8V²`. -/
theorem eventually_completeWeilEnergy_ge_beyond_gcd {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hmass : 0 < ∫ u, φ u ^ 2) {ε V η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log N ^ (1 / 4 : ℝ) →
      ∀ M : ℕ, 0 < M → M ≤ admissiblePeriod N → ∀ F : ℕ → ℝ, Function.Periodic F M →
      (∀ n, |F n| ≤ V) → (∃ n₀, η ≤ |F n₀ - F (n₀.gcd M)|) →
        η ^ 2 * Real.log N / (16 * M ^ 2) ≤ jumpEnergy N (neutralCharge F N) ∧
        (1 - ε) * jumpEnergy N (neutralCharge F N) ≤
          completeWeilEnergy φ c N (packetVector (neutralCharge F N) N) ∧
        ‖packetVector (neutralCharge F N) N‖ ^ 2 ≤ 8 * V ^ 2 := by
  obtain ⟨A, B, hA, hB, hbound⟩ := exists_complete_packet_two_moment_bound hφ hφ0 hsupp hmass
  set K : ℝ := (128 * V ^ 2 * (A + B) + 1) / (ε * η ^ 2) with hKdef
  have hK : 0 < K := by positivity
  filter_upwards [eventually_beyond_gcd_scales hK] with N ⟨hL, hN3, hKN⟩
  intro c hc1 hcL M hM hMN F hper hV ⟨n₀, hn₀⟩
  have hL0 : 0 < Real.log N := by linarith only [hL]
  have hL1 : 1 ≤ Real.log N := by linarith only [hL]
  have hN1 : 1 ≤ N := by
    by_contra h
    have hN0 : N = 0 := by omega
    rw [hN0, Nat.cast_zero, Real.log_zero] at hL0
    exact lt_irrefl 0 hL0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  -- the jump energy
  have hJF := jumpEnergy_ge_beyond_gcd hM hMN hL hper hη.le hn₀
  have hJG : η ^ 2 * Real.log N / (16 * M ^ 2) ≤ jumpEnergy N (neutralCharge F N) := by
    rw [jumpEnergy_neutralCharge F hL0, le_div_iff₀ hL0]
    calc η ^ 2 * Real.log N / (16 * M ^ 2) * Real.log N
        = η ^ 2 * Real.log N ^ 2 / (16 * M ^ 2) := by ring
      _ ≤ jumpEnergy N F := hJF
  have hnorm := norm_sq_packetVector_neutralCharge_le hV hN1 hL1
  refine ⟨hJG, ?_, hnorm⟩
  -- the two-moment remainder
  have hcN : c / N ≤ 1 / 3 := by
    rw [div_le_iff₀ hN0]
    linarith only [hcL, hN3]
  have hrem := hbound c N hc1 hN1 hcN (neutralCharge F N) (sum_neutralCharge_div hN1)
  rw [← packetVector_norm_sq] at hrem
  have hsq := sum_sq_neutralCharge_le hV hN1 hL0
  have hc3 : c ^ 3 ≤ Real.log N ^ (3 / 4 : ℝ) := by
    have hpow : (Real.log N ^ (1 / 4 : ℝ)) ^ 3 = Real.log N ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      norm_num
    exact (pow_le_pow_left₀ (by linarith only [hc1]) hcL 3).trans_eq hpow
  have hc23 : c ^ 2 ≤ c ^ 3 := by
    have := mul_le_mul_of_nonneg_left hc1 (sq_nonneg c)
    nlinarith only [this]
  have hterm1 : A * c ^ 2 * ‖packetVector (neutralCharge F N) N‖ ^ 2 ≤ 8 * V ^ 2 * A * c ^ 3 := by
    calc A * c ^ 2 * ‖packetVector (neutralCharge F N) N‖ ^ 2 ≤ A * c ^ 3 * (8 * V ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hc23 hA) hnorm (sq_nonneg _) (by positivity)
      _ = 8 * V ^ 2 * A * c ^ 3 := by ring
  have hterm2 : B * c ^ 3 * (Real.log N + 1) / N * ∑ n ∈ Icc 1 N, neutralCharge F N n ^ 2 ≤
      8 * V ^ 2 * B * c ^ 3 := by
    have hc30 : 0 ≤ B * c ^ 3 * (Real.log N + 1) / N := by positivity
    calc B * c ^ 3 * (Real.log N + 1) / N * ∑ n ∈ Icc 1 N, neutralCharge F N n ^ 2
        ≤ B * c ^ 3 * (Real.log N + 1) / N * (4 * V ^ 2 * N / Real.log N) :=
          mul_le_mul_of_nonneg_left hsq hc30
      _ = 4 * V ^ 2 * B * c ^ 3 * ((Real.log N + 1) / Real.log N) := by
          field_simp
      _ ≤ 4 * V ^ 2 * B * c ^ 3 * 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_iff₀ hL0]
          linarith only [hL1]
      _ = 8 * V ^ 2 * B * c ^ 3 := by ring
  have herr : |completeWeilEnergy φ c N (packetVector (neutralCharge F N) N) -
      jumpEnergy N (neutralCharge F N)| ≤ 8 * V ^ 2 * (A + B) * Real.log N ^ (3 / 4 : ℝ) := by
    refine hrem.trans ?_
    have h8 : 0 ≤ 8 * V ^ 2 * (A + B) := by positivity
    calc A * c ^ 2 * ‖packetVector (neutralCharge F N) N‖ ^ 2 +
          B * c ^ 3 * (Real.log N + 1) / N * ∑ n ∈ Icc 1 N, neutralCharge F N n ^ 2
        ≤ 8 * V ^ 2 * A * c ^ 3 + 8 * V ^ 2 * B * c ^ 3 := add_le_add hterm1 hterm2
      _ = 8 * V ^ 2 * (A + B) * c ^ 3 := by ring
      _ ≤ 8 * V ^ 2 * (A + B) * Real.log N ^ (3 / 4 : ℝ) := mul_le_mul_of_nonneg_left hc3 h8
  -- the remainder is an `ε` fraction of the jump energy
  obtain ⟨hMlog, -⟩ := admissiblePeriod_spec hM hMN
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hM2 : (M : ℝ) ^ 2 ≤ Real.log (Real.log N) ^ 2 := pow_le_pow_left₀ hM0.le hMlog 2
  have hll0 : 0 < Real.log (Real.log N) := hM0.trans_le hMlog
  have hsplit : Real.log N ^ (3 / 4 : ℝ) * Real.log N ^ (1 / 4 : ℝ) = Real.log N := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hsmall : 8 * V ^ 2 * (A + B) * Real.log N ^ (3 / 4 : ℝ) ≤
      ε * (η ^ 2 * Real.log N / (16 * M ^ 2)) := by
    have hp34 : 0 < Real.log N ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hL0 _
    have hεη : 0 < ε * η ^ 2 := by positivity
    have hKN' : (128 * V ^ 2 * (A + B) + 1) * Real.log (Real.log N) ^ 2 ≤
        ε * η ^ 2 * Real.log N ^ (1 / 4 : ℝ) := by
      rw [hKdef, div_mul_eq_mul_div, div_le_iff₀ hεη] at hKN
      linarith only [hKN]
    rw [show ε * (η ^ 2 * Real.log N / (16 * M ^ 2)) = ε * η ^ 2 * Real.log N / (16 * M ^ 2) by ring,
      le_div_iff₀ (by positivity)]
    have hV0 : 0 ≤ 128 * V ^ 2 * (A + B) := by positivity
    calc 8 * V ^ 2 * (A + B) * Real.log N ^ (3 / 4 : ℝ) * (16 * M ^ 2)
        = 128 * V ^ 2 * (A + B) * M ^ 2 * Real.log N ^ (3 / 4 : ℝ) := by ring
      _ ≤ (128 * V ^ 2 * (A + B) + 1) * Real.log (Real.log N) ^ 2 * Real.log N ^ (3 / 4 : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hp34.le
          exact mul_le_mul (by linarith only) hM2 (sq_nonneg _) (by positivity)
      _ ≤ ε * η ^ 2 * Real.log N ^ (1 / 4 : ℝ) * Real.log N ^ (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right hKN' hp34.le
      _ = ε * η ^ 2 * Real.log N := by rw [mul_assoc, mul_comm (Real.log N ^ (1 / 4 : ℝ)), hsplit]
  have hεJ := mul_le_mul_of_nonneg_left hJG hε.le
  have hlow := (abs_le.mp herr).1
  nlinarith only [hlow, hsmall, hεJ]

/-- **Coercivity beyond the gcd profiles.** Eventually, along `1 ≤ c ≤ (log N)^{1/4}`, every neutral
charge of period `M ≤ M₀(N)` with `|F| ≤ V` and gcd defect `≥ η` has
`W(u) ≥ η² log N / (256 V² (log log N)²) · ‖u‖²`. -/
theorem eventually_completeWeilEnergy_coercive_beyond_gcd {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hmass : 0 < ∫ u, φ u ^ 2) {V η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log N ^ (1 / 4 : ℝ) →
      ∀ M : ℕ, 0 < M → M ≤ admissiblePeriod N → ∀ F : ℕ → ℝ, Function.Periodic F M →
      (∀ n, |F n| ≤ V) → (∃ n₀, η ≤ |F n₀ - F (n₀.gcd M)|) →
        η ^ 2 * Real.log N / (256 * V ^ 2 * Real.log (Real.log N) ^ 2) *
            ‖packetVector (neutralCharge F N) N‖ ^ 2 ≤
          completeWeilEnergy φ c N (packetVector (neutralCharge F N) N) := by
  filter_upwards [eventually_completeWeilEnergy_ge_beyond_gcd hφ hφ0 hsupp hmass
    (by norm_num : (0 : ℝ) < 1 / 2) hη (V := V)] with N hN
  intro c hc1 hcL M hM hMN F hper hV hdef
  obtain ⟨hJ, hW, hnorm⟩ := hN c hc1 hcL M hM hMN F hper hV hdef
  obtain ⟨n₀, hn₀⟩ := hdef
  obtain ⟨hMlog, -⟩ := admissiblePeriod_spec hM hMN
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hll0 : 0 < Real.log (Real.log N) := hM0.trans_le hMlog
  -- `V ≥ η/2 > 0`
  have hV2 : η ≤ 2 * V := by
    have h := hn₀.trans (abs_sub _ _)
    linarith only [h, hV n₀, hV (n₀.gcd M)]
  have hV0 : 0 < V := by linarith only [hV2, hη]
  have hM2 : (M : ℝ) ^ 2 ≤ Real.log (Real.log N) ^ 2 := pow_le_pow_left₀ hM0.le hMlog 2
  have hL0 : 0 < Real.log N := by
    have h0 := Real.log_natCast_nonneg N
    by_contra h
    have h1 := Real.log_nonpos h0 (by linarith only [h])
    linarith only [h1, hll0]
  have hJlow : η ^ 2 * Real.log N / (32 * Real.log (Real.log N) ^ 2) ≤
      completeWeilEnergy φ c N (packetVector (neutralCharge F N) N) := by
    have h1 : η ^ 2 * Real.log N / (16 * Real.log (Real.log N) ^ 2) ≤
        η ^ 2 * Real.log N / (16 * M ^ 2) :=
      div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg η) hL0.le) (by positivity)
        (by linarith only [hM2])
    have h2 : η ^ 2 * Real.log N / (32 * Real.log (Real.log N) ^ 2) =
        (1 - 1 / 2) * (η ^ 2 * Real.log N / (16 * Real.log (Real.log N) ^ 2)) := by
      field_simp
      ring
    rw [h2]
    exact (mul_le_mul_of_nonneg_left (h1.trans hJ) (by norm_num)).trans hW
  refine le_trans ?_ hJlow
  have hcoef : 0 ≤ η ^ 2 * Real.log N / (256 * V ^ 2 * Real.log (Real.log N) ^ 2) :=
    div_nonneg (mul_nonneg (sq_nonneg η) hL0.le) (by positivity)
  calc η ^ 2 * Real.log N / (256 * V ^ 2 * Real.log (Real.log N) ^ 2) *
        ‖packetVector (neutralCharge F N) N‖ ^ 2
      ≤ η ^ 2 * Real.log N / (256 * V ^ 2 * Real.log (Real.log N) ^ 2) * (8 * V ^ 2) :=
        mul_le_mul_of_nonneg_left hnorm hcoef
    _ = η ^ 2 * Real.log N / (32 * Real.log (Real.log N) ^ 2) := by
        field_simp
        ring

end GaloisForLFunctions.ArithmeticCouplingTheory
