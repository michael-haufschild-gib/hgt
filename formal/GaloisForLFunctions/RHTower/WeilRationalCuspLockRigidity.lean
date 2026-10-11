import GaloisForLFunctions.RHTower.WeilRationalCuspLockSpectrum

/-!
# One-sided rational resonances force the true producer

**Theorem** (`one_sided_rational_lock_rigidity`).  Let `G` be a Herglotz producer for the weights
`lam`.  Suppose that on the lower critical line

`G(1 − s) = (Σ_k P(k) k^{−(s−½)} + Σ_j c_j u_j^{−(s−½)}) G(s)`,

where `Σ|P(k)| < ∞`, `u_j > 0`, `Σ_j |c_j| max(1, u_j^{−1}) < ∞`, and every rational `u_j` is a
non-integer `> 1`.  The irrational `u_j` are arbitrary.  Then `lam(n) = Λ(n)` for all `n ≥ 2`, and
the Riemann hypothesis holds.

On the line `s = ½ − iy` the lock is an almost-periodic function whose rational frequencies
`log u` all have `u ≥ 1`: the one-sided case of the rational resonance problem.  The
non-Herglotz producer `(1 + c n₀^{½−s}) ξ` has the frequency `u = 1/n₀ < 1`, so one-sidedness
is essential to this argument.

**Proof.**
1. The twisted radial limit at real height `x` is `√x Σ_n a(n) n^{−1/2} R(x/n)` for non-integer
   `x`, where `R(r) = Σ_{u_j = r} c_j` (`tendsto_far_real_height`), and it is period-one in `x`
   (`tendsto_far_translation`).
2. For rational `x ∈ (0, 1)` every `x/n` is a rational `< 1`, so `R(x/n) = 0` and the limit
   vanishes.  By periodicity it vanishes at every non-integer rational height.
3. Since `a(1) = 1`, `R(y) = −Σ_{n ≥ 2} a(n) n^{−1/2} R(y/n)`.  Induction on `⌊y⌋` gives `R(y) = 0`
   for every non-integer rational `y`.
4. The second family therefore has vanishing aggregated coefficients at every positive rational,
   and `aggregated_resonant_lock_rigidity` applies.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity
  HamburgerTwisted WeilSpectral

noncomputable section

/-- The coefficients of the family `(c, u)` aggregated at the value `r`. -/
def aggCoeff (c : ℕ → ℂ) (u : ℕ → ℝ) (r : ℝ) : ℂ := ∑' j, if u j = r then c j else 0

theorem halfCoeff_zero (a : ℕ → ℂ) : halfCoeff a 0 = 0 := by
  simp [halfCoeff]

theorem halfCoeff_one_dirichletExp (lam : ℕ → ℝ) :
    halfCoeff (dirichletExp (lamLog lam)) 1 = 1 := by
  rw [halfCoeff, dirichletExp_one (lamLog_zero lam) (lamLog_one lam)]
  simp

/-- The resonance sum at a non-integer height. -/
theorem ratSpec_of_not_nat (P c : ℕ → ℂ) (u : ℕ → ℝ) {x : ℝ} (hx : 0 < x)
    (hxn : ∀ k : ℕ, x ≠ k) {n : ℕ} (hn : 1 ≤ n) :
    ratSpec P c u x n = (n : ℂ) * aggCoeff c u (x / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold ratSpec aggCoeff
  have h1 : (∑' k : ℕ, if (n : ℝ) * (((k : ℝ) + 1) / x) = ((1 : ℕ) : ℝ) then (n : ℂ) * P (k + 1)
      else 0) = 0 := by
    refine (tsum_congr fun k => if_neg fun h => hxn (n * (k + 1)) ?_).trans tsum_zero
    rw [Nat.cast_one, mul_div_assoc', div_eq_one_iff_eq hx.ne'] at h
    push_cast; linarith
  rw [h1, zero_add, ← tsum_mul_left]
  congr 1; funext j
  have hiff : (n : ℝ) * (u j / x) = ((1 : ℕ) : ℝ) ↔ u j = x / n := by
    rw [Nat.cast_one, eq_div_iff hn0.ne', mul_div_assoc', div_eq_one_iff_eq hx.ne']
    constructor <;> intro h <;> linarith
  by_cases h : u j = x / n
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero]

/-- The height-`x` resonance sum in terms of the aggregated coefficients. -/
theorem tsum_term_ratSpec (lam : ℕ → ℝ) (P c : ℕ → ℂ) (u : ℕ → ℝ) {x : ℝ} (hx : 0 < x)
    (hxn : ∀ k : ℕ, x ≠ k) :
    ∑' n, LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n * ratSpec P c u x n =
      ∑' n, halfCoeff (dirichletExp (lamLog lam)) n * aggCoeff c u (x / n) := by
  congr 1; funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [halfCoeff_zero]
  rw [ratSpec_of_not_nat P c u hx hxn (Nat.one_le_iff_ne_zero.mpr hn), ← mul_assoc,
    term_three_halves_mul _ hn]

/-! ### The induction -/

/-- If every rational `u_j` is a non-integer `> 1`, the aggregated coefficient vanishes at every
rational below one and at every integer. -/
theorem aggCoeff_eq_zero_of_not_mem {c : ℕ → ℂ} {u : ℕ → ℝ} {r : ℝ} (hr : ∀ j, u j ≠ r) :
    aggCoeff c u r = 0 :=
  (tsum_congr fun j => if_neg (hr j)).trans tsum_zero

/-- **Vanishing of the rational coefficients.**  If `Σ_n a(n) n^{−1/2} R(y/n) = 0` at every
non-integer positive rational `y`, `a(1) = 1`, and `R` vanishes at rationals below one, then `R`
vanishes at every non-integer positive rational. -/
theorem aggCoeff_eq_zero_of_system {b : ℕ → ℂ} (hb0 : b 0 = 0) (hb1 : b 1 = 1) {R : ℝ → ℂ}
    (hRlt : ∀ q : ℚ, 0 < q → q < 1 → R q = 0)
    (hsys : ∀ q : ℚ, 0 < q → (∀ k : ℕ, (q : ℝ) ≠ k) → ∑' n, b n * R ((q : ℝ) / n) = 0)
    (hbsum : ∀ q : ℚ, Summable fun n => b n * R ((q : ℝ) / n)) :
    ∀ N : ℕ, ∀ q : ℚ, 0 < q → (q : ℝ) < N → (∀ k : ℕ, (q : ℝ) ≠ k) → R q = 0 := by
  intro N
  induction N with
  | zero =>
    intro q hq hqN _
    have : (0 : ℝ) < q := by exact_mod_cast hq
    simp at hqN; linarith
  | succ N ih =>
    intro q hq hqN hqk
    by_cases hq1 : q < 1
    · exact hRlt q hq hq1
    push Not at hq1
    have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have hs := hsys q hq hqk
    rw [(hbsum q).tsum_eq_zero_add, hb0, zero_mul, zero_add,
      (((summable_nat_add_iff 1).mpr (hbsum q))).tsum_eq_zero_add] at hs
    simp only [zero_add, Nat.cast_one, div_one, hb1, one_mul] at hs
    have hrest : (∑' n : ℕ, b (n + 1 + 1) * R ((q : ℝ) / ((n + 1 + 1 : ℕ) : ℝ))) = 0 := by
      refine (tsum_congr fun n => ?_).trans tsum_zero
      have hn2 : (2 : ℝ) ≤ ((n + 1 + 1 : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hpos : (0 : ℝ) < ((n + 1 + 1 : ℕ) : ℝ) := by linarith
      set q' : ℚ := q / ((n + 1 + 1 : ℕ) : ℚ) with hq'
      have hq'r : ((q' : ℚ) : ℝ) = (q : ℝ) / ((n + 1 + 1 : ℕ) : ℝ) := by
        rw [hq']; push_cast; ring
      rw [← hq'r]
      have hq'pos : 0 < q' := by rw [hq']; positivity
      have hq'N : ((q' : ℚ) : ℝ) < N := by
        rw [hq'r, div_lt_iff₀ hpos]
        have hqN' : (q : ℝ) < N + 1 := by exact_mod_cast hqN
        have hN1 : (1 : ℝ) ≤ N := by
          have : (1 : ℝ) < N + 1 := lt_of_le_of_lt hq1' hqN'
          by_contra hcon; push Not at hcon
          have hN0 : N = 0 := by
            have : (N : ℝ) < 1 := hcon
            exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
          subst hN0; simp at this
        nlinarith
      have hq'k : ∀ k : ℕ, ((q' : ℚ) : ℝ) ≠ k := by
        intro k hk
        rw [hq'r, div_eq_iff hpos.ne'] at hk
        exact hqk (k * (n + 1 + 1)) (by rw [hk]; push_cast; ring)
      rw [ih q' hq'pos hq'N hq'k, mul_zero]
    rw [hrest, add_zero] at hs
    exact hs

/-! ### The rigidity theorem -/

/-- **One-sided rational resonances force the true producer.** -/
theorem one_sided_rational_lock_rigidity {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖) {c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹)
    (hrat : ∀ j (a b : ℕ), 0 < b → (b : ℝ) * u j = a → b < a ∧ ¬ b ∣ a)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      (LSeries P (lineS τ - 1 / 2) + ∑' j, c j * (u j : ℂ) ^ (-(lineS τ - 1 / 2))) * G (lineS τ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  have hlockV : ∀ τ : ℝ, τ < 0 →
      G (1 - lineS τ) = (dirLock P (lineS τ) + apLock c u (lineS τ)) * G (lineS τ) := by
    intro τ hτ
    rw [dirLock_of_le P (le_of_eq (lineS_re τ).symm),
      apLock_of_mem c u (le_of_eq (lineS_re τ).symm) (by rw [lineS_re]; norm_num)]
    exact hlock τ hτ
  set a := dirichletExp (lamLog lam) with ha
  -- rational values that no `u_j` takes
  have hne_q : ∀ j (q : ℚ), 0 < q → (q : ℝ) ≤ 1 → u j ≠ q := by
    intro j q hq hq1 he
    have hnum : 0 < q.num := Rat.num_pos.mpr hq
    have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hnat : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
      have := Int.toNat_of_nonneg hnum.le
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    have hcast : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
    have hb := hrat j q.num.toNat q.den q.den_pos (by
      rw [he, hcast, hnat]; field_simp)
    have hlt : (q.den : ℝ) < ((q.num.toNat : ℕ) : ℝ) := by exact_mod_cast hb.1
    rw [hnat] at hlt
    rw [hcast, div_le_one hden] at hq1
    linarith
  have hne_nat : ∀ j (k : ℕ), u j ≠ k := by
    intro j k he
    have hb := hrat j k 1 one_pos (by rw [he]; simp)
    exact hb.2 (one_dvd k)
  -- the period-one law of the resonance sums
  have hL : ∀ x : ℝ, 0 < x →
      ((Real.sqrt (x + 1) : ℝ) : ℂ) * ∑' n, LSeries.term a (((3 / 2 : ℝ) : ℂ)) n *
          ratSpec P c u (x + 1) n =
        ((Real.sqrt x : ℝ) : ℂ) * ∑' n, LSeries.term a (((3 / 2 : ℝ) : ℂ)) n * ratSpec P c u x n := by
    intro x hx
    have h1 := tendsto_far_real_height hsl hΦre hidT hGc hGd hG2 hP hu hc hlockV
      (x := x + 1) (by linarith)
    have h0 := tendsto_far_real_height hsl hΦre hidT hGc hGd hG2 hP hu hc hlockV hx
    have ht := tendsto_far_translation hsl hΦre hidT hGc hGd hG2 hx
    have hd := h1.sub h0
    refine sub_eq_zero.mp (tendsto_nhds_unique hd (ht.congr fun ε => ?_))
    rw [mul_sub]
  set S : ℝ → ℂ := fun x => ∑' n, halfCoeff a n * aggCoeff c u (x / n) with hS
  -- the sums vanish below one
  have hS01 : ∀ q : ℚ, 0 < q → q < 1 → S q = 0 := by
    intro q hq hq1
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rcases eq_or_ne n 0 with rfl | hn
    · simp [halfCoeff_zero]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hq1' : (q : ℝ) < 1 := by exact_mod_cast hq1
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
    rw [aggCoeff_eq_zero_of_not_mem (r := (q : ℝ) / n) fun j => by
      have := hne_q j (q / n) (by positivity) (by
        push_cast
        rw [div_le_one (by linarith)]; linarith)
      push_cast at this; exact this, mul_zero]
  -- hence at every non-integer positive rational
  have hSall : ∀ q : ℚ, 0 < q → (∀ k : ℕ, (q : ℝ) ≠ k) → S q = 0 := by
    have hshift : ∀ k : ℕ, ∀ q : ℚ, 0 < q → q < 1 →
        ((Real.sqrt ((q : ℝ) + k) : ℝ) : ℂ) * S ((q : ℝ) + k) = 0 := by
      intro k q hq hq1
      have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
      have hnotnat : ∀ j : ℕ, ∀ m : ℕ, (q : ℝ) + j ≠ m := by
        intro j m he
        have hq1' : (q : ℝ) < 1 := by exact_mod_cast hq1
        have hfl : (m : ℝ) - j = q := by linarith
        have hm : j < m := by
          have : (j : ℝ) < m := by linarith
          exact_mod_cast this
        have : ((m - j : ℕ) : ℝ) = q := by rw [Nat.cast_sub hm.le]; exact hfl
        have hlt : ((m - j : ℕ) : ℝ) < 1 := by rw [this]; exact hq1'
        have hpos : (0 : ℝ) < ((m - j : ℕ) : ℝ) := by rw [this]; exact hqpos
        have h1 : m - j < 1 := by exact_mod_cast hlt
        have h2 : 0 < m - j := by exact_mod_cast hpos
        omega
      induction k with
      | zero =>
        simp only [Nat.cast_zero, add_zero]
        rw [hS01 q hq hq1, mul_zero]
      | succ k ih =>
        have hx : (0 : ℝ) < (q : ℝ) + k := by positivity
        have hL' := hL ((q : ℝ) + k) hx
        rw [tsum_term_ratSpec lam P c u (by linarith) (fun m => by
            have := hnotnat (k + 1) m; push_cast at this; rw [add_assoc]; exact this),
          tsum_term_ratSpec lam P c u hx (hnotnat k)] at hL'
        push_cast
        rw [← add_assoc]
        exact hL'.trans ih
    intro q hq hqk
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
    set k : ℕ := ⌊(q : ℝ)⌋₊ with hk
    have hkle : (k : ℝ) ≤ q := Nat.floor_le hqpos.le
    have hklt : (q : ℝ) < k + 1 := Nat.lt_floor_add_one _
    set q' : ℚ := q - k with hq'
    have hq'r : ((q' : ℚ) : ℝ) = (q : ℝ) - k := by rw [hq']; push_cast; ring
    have hq'pos : 0 < q' := by
      have : (0 : ℝ) < (q : ℝ) - k := by
        rcases hkle.lt_or_eq with h | h
        · linarith
        · exact absurd h.symm (hqk k)
      rw [← hq'r] at this; exact_mod_cast this
    have hq'1 : q' < 1 := by
      have : (q : ℝ) - k < 1 := by linarith
      rw [← hq'r] at this; exact_mod_cast this
    have h := hshift k q' hq'pos hq'1
    rw [hq'r, sub_add_cancel] at h
    have hsq : ((Real.sqrt q : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.mpr hqpos).ne'
    exact (mul_eq_zero.mp h).resolve_left hsq
  -- the aggregated coefficients vanish at every non-integer rational
  have hRall : ∀ q : ℚ, 0 < q → (∀ k : ℕ, (q : ℝ) ≠ k) → aggCoeff c u q = 0 := by
    have hfin : ∀ q : ℚ, Summable fun n : ℕ => halfCoeff a n * aggCoeff c u ((q : ℝ) / n) := by
      intro q
      refine summable_of_ne_finset_zero (s := Finset.range (⌈(q : ℝ)⌉₊ + 1)) fun n hn => ?_
      rw [Finset.mem_range, not_lt] at hn
      rcases eq_or_ne n 0 with rfl | hn0
      · simp [halfCoeff_zero]
      have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
      have hqn : (q : ℝ) / n ≤ 1 := by
        rw [div_le_one hnpos]
        have h1 : (q : ℝ) ≤ ⌈(q : ℝ)⌉₊ := Nat.le_ceil _
        have h2 : ((⌈(q : ℝ)⌉₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hn
        linarith
      rw [aggCoeff_eq_zero_of_not_mem (r := (q : ℝ) / n) fun j => ?_, mul_zero]
      by_cases hq0 : 0 < q
      · have := hne_q j (q / n) (by positivity) (by push_cast; exact hqn)
        push_cast at this; exact this
      · intro he
        have hqnp : (q : ℝ) / n ≤ 0 := by
          have : (q : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp hq0
          exact div_nonpos_of_nonpos_of_nonneg this hnpos.le
        linarith [hu j]
    intro q hq hqk
    have hmain := aggCoeff_eq_zero_of_system (b := halfCoeff a) (halfCoeff_zero a)
      (halfCoeff_one_dirichletExp lam) (R := aggCoeff c u)
      (fun q hq hq1 => aggCoeff_eq_zero_of_not_mem fun j => hne_q j q hq (by
        have : (q : ℝ) < 1 := by exact_mod_cast hq1
        linarith))
      (fun q hq hqk => hSall q hq hqk) hfin
    exact hmain (⌈(q : ℝ)⌉₊ + 1) q hq (by
      have := Nat.le_ceil (q : ℝ); push_cast; linarith) hqk
  -- the aggregated vanishing hypothesis of the integral theorem
  have hagg : ∀ a' b : ℕ, 0 < b → (∑' j, if (b : ℝ) * u j = a' then c j else 0) = 0 := by
    intro a' b hb
    by_cases hex : ∃ j, (b : ℝ) * u j = a'
    · obtain ⟨j₀, hj₀⟩ := hex
      obtain ⟨hlt, hndvd⟩ := hrat j₀ a' b hb hj₀
      have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
      set q : ℚ := (a' : ℚ) / b with hq
      have hqr : ((q : ℚ) : ℝ) = (a' : ℝ) / b := by rw [hq]; push_cast; ring
      have ha'pos : 0 < a' := by omega
      have hqpos : 0 < q := by
        rw [hq]; exact div_pos (by exact_mod_cast ha'pos) (by exact_mod_cast hb)
      have hqk : ∀ k : ℕ, (q : ℝ) ≠ k := by
        intro k hk
        rw [hqr, div_eq_iff hbpos.ne'] at hk
        have hk' : (a' : ℝ) = ((b * k : ℕ) : ℝ) := by rw [hk]; push_cast; ring
        exact hndvd ⟨k, by exact_mod_cast hk'⟩
      have h0 := hRall q hqpos hqk
      rw [hqr] at h0
      unfold aggCoeff at h0
      refine Eq.trans ?_ h0
      congr 1; funext j
      have hiff : (b : ℝ) * u j = a' ↔ u j = (a' : ℝ) / b := by
        rw [eq_div_iff hbpos.ne']; constructor <;> intro h <;> linarith
      by_cases h : (b : ℝ) * u j = a'
      · rw [if_pos h, if_pos (hiff.mp h)]
      · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
    · push Not at hex
      exact (tsum_congr fun j => if_neg (hex j)).trans tsum_zero
  exact aggregated_resonant_lock_rigidity hsl hΦd hΦre hid hGc hGd hG2 hP hu hc hagg hlock

end

end AbelianTwist

end RHTower
