import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.TheBezoutTheoremOfTheMultiplicativeGroup

/-!
# The Riemann–Roch theorem of the multiplicative group of `ℚ`

The Bézout theorem bounds the vanishing of a Dirichlet polynomial along Frobenius progressions.
Its exact form is a dimension count. Call a **section of length `N` with divisor `m`** a Dirichlet
polynomial `Σ_{n≤N} a_n n^{−s}` vanishing to order `m_p` along the progression of every `p ∈ S`
(`sections`). Then

> **Riemann–Roch** (`finrank_sections`): `h⁰(N, m) = dim sections N S m = ⌊N/∏_{p∈S} p^{m_p}⌋`.

The two sides of one division step are inverse linear maps (`sectionsEquivQuot`): multiplication by
the Euler factor `1 − p^{−s}` (`eulerMul`) and the tower quotient (`towerQuot`), between sections of
length `N` with divisor `m` and sections of length `⌊N/p⌋` with divisor `m − e_p`. With no conditions
the sections are all Dirichlet polynomials of length `N` (`finrank_dirPolys`), so `h⁰(N, 0) = N`,
the box-class size. A section count, defined without any sign, obeys the exact law
`h⁰ = ⌊e^{deg}⌋` with `deg = log N − Σ m_p log p`; it is positive iff the degree is nonnegative
(`sections_ne_bot_iff`), which is Bézout with its converse.

This is the Riemann–Roch of the base: one dimension, exact, and linear in `e^{deg}`. Over `𝔽_q[T]`
the same count is additive (`finrank_divisibleLT_eulerFactor`): a Dirichlet polynomial of length
`q^d` is a polynomial of degree `≤ d` in `u = q^{−s}`, and vanishing to order `m` along the
progression of a place of degree `e` costs `em` conditions, shared by all places of that degree.
Over `ℤ` every prime has its own progression and vanishing along it costs `N − ⌊N/p⌋` conditions.
The Hodge index needs a surface with a quadratic Euler characteristic; the theorem fixes what the
fibres of such a surface over the base must count.
-/

open Complex Finset Filter

noncomputable section

namespace GaloisForLFunctions.EffectiveArithmeticHodgeTheory

/-! ### Linearity -/

theorem dirDeriv_add (a b : ℕ → ℂ) (N i : ℕ) (s : ℂ) :
    dirDeriv (a + b) N i s = dirDeriv a N i s + dirDeriv b N i s := by
  simp only [dirDeriv, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dirDeriv_smul (c : ℂ) (a : ℕ → ℂ) (N i : ℕ) (s : ℂ) :
    dirDeriv (c • a) N i s = c * dirDeriv a N i s := by
  simp only [dirDeriv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem dirDeriv_zero (N i : ℕ) (s : ℂ) : dirDeriv 0 N i s = 0 := by
  simp [dirDeriv]

theorem VanishesAlong.add {a b : ℕ → ℂ} {N p m : ℕ} (ha : VanishesAlong a N p m)
    (hb : VanishesAlong b N p m) : VanishesAlong (a + b) N p m := fun i hi => by
  filter_upwards [ha i hi, hb i hi] with j h1 h2
  rw [dirDeriv_add, h1, h2, add_zero]

theorem VanishesAlong.smul {a : ℕ → ℂ} {N p m : ℕ} (ha : VanishesAlong a N p m) (c : ℂ) :
    VanishesAlong (c • a) N p m := fun i hi => by
  filter_upwards [ha i hi] with j h
  rw [dirDeriv_smul, h, mul_zero]

theorem vanishesAlong_zero_fun (N p m : ℕ) : VanishesAlong 0 N p m := fun _ _ =>
  Eventually.of_forall fun _ => dirDeriv_zero _ _ _

theorem vanishesAlong_zero_order (a : ℕ → ℂ) (N p : ℕ) : VanishesAlong a N p 0 := fun _ hi =>
  absurd hi (Nat.not_lt_zero _)

/-! ### Sections -/

/-- **Sections of length `N` with divisor `m` on `S`**: coefficient sequences supported in
`[1, N]` whose Dirichlet polynomial vanishes to order `m_p` along the progression of every
`p ∈ S`. -/
def sections (N : ℕ) (S : Finset ℕ) (m : ℕ → ℕ) : Submodule ℂ (ℕ → ℂ) where
  carrier := {a | a 0 = 0 ∧ (∀ n, N < n → a n = 0) ∧ ∀ p ∈ S, VanishesAlong a N p (m p)}
  add_mem' := fun {a b} ha hb => ⟨by simp [ha.1, hb.1], fun n hn => by
    simp [ha.2.1 n hn, hb.2.1 n hn], fun p hp => (ha.2.2 p hp).add (hb.2.2 p hp)⟩
  zero_mem' := ⟨rfl, fun _ _ => rfl, fun p _ => vanishesAlong_zero_fun _ _ _⟩
  smul_mem' := fun c a ha => ⟨by simp [ha.1], fun n hn => by simp [ha.2.1 n hn],
    fun p hp => (ha.2.2 p hp).smul c⟩

/-- The Dirichlet polynomials of length `N`. -/
def dirPolys (N : ℕ) : Submodule ℂ (ℕ → ℂ) where
  carrier := {a | a 0 = 0 ∧ ∀ n, N < n → a n = 0}
  add_mem' := fun {a b} ha hb => ⟨by simp [ha.1, hb.1], fun n hn => by
    simp [ha.2 n hn, hb.2 n hn]⟩
  zero_mem' := ⟨rfl, fun _ _ => rfl⟩
  smul_mem' := fun c a ha => ⟨by simp [ha.1], fun n hn => by simp [ha.2 n hn]⟩

/-- Dirichlet polynomials of length `N` are their `N` coefficients. -/
def dirPolysEquiv (N : ℕ) : dirPolys N ≃ₗ[ℂ] (Fin N → ℂ) where
  toFun a i := (a : ℕ → ℂ) ((i : ℕ) + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨fun n => if h : 1 ≤ n ∧ n ≤ N then v ⟨n - 1, by omega⟩ else 0,
    ⟨by simp, fun n hn => dif_neg fun h => by omega⟩⟩
  left_inv a := by
    refine Subtype.ext (funext fun n => ?_)
    show (if h : 1 ≤ n ∧ n ≤ N then (a : ℕ → ℂ) (n - 1 + 1) else 0) = (a : ℕ → ℂ) n
    split_ifs with h
    · rw [Nat.sub_add_cancel h.1]
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact a.2.1.symm
      · have : N < n := by
          by_contra hc
          exact h ⟨hn, not_lt.mp hc⟩
        exact (a.2.2 n this).symm
  right_inv v := by
    funext i
    show (if h : 1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ N then v ⟨(i : ℕ) + 1 - 1, by omega⟩ else 0) = v i
    rw [dif_pos ⟨Nat.le_add_left 1 _, i.2⟩]
    exact congrArg v (Fin.ext (by simp))

instance (N : ℕ) : FiniteDimensional ℂ (dirPolys N) :=
  Module.Finite.equiv (dirPolysEquiv N).symm

/-- **`h⁰(N, 0) = N`**: the box-class size. -/
theorem finrank_dirPolys (N : ℕ) : Module.finrank ℂ (dirPolys N) = N := by
  rw [(dirPolysEquiv N).finrank_eq, Module.finrank_fin_fun]

theorem sections_le_dirPolys (N : ℕ) (S : Finset ℕ) (m : ℕ → ℕ) : sections N S m ≤ dirPolys N :=
  fun _ ha => ⟨ha.1, ha.2.1⟩

instance (N : ℕ) (S : Finset ℕ) (m : ℕ → ℕ) : FiniteDimensional ℂ (sections N S m) :=
  Submodule.finiteDimensional_of_le (sections_le_dirPolys N S m)

theorem sections_eq_dirPolys {N : ℕ} {S : Finset ℕ} {m : ℕ → ℕ} (hm : ∀ p ∈ S, m p = 0) :
    sections N S m = dirPolys N := by
  ext a
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun p hp => by
    rw [hm p hp]; exact vanishesAlong_zero_order _ _ _⟩⟩

/-! ### Multiplication by the Euler factor -/

/-- Multiplication by `1 − p^{−s}`: `(EF)(n) = F(n) − F(n/p)·[p ∣ n]`. -/
def eulerMul (p : ℕ) (F : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else F n - if p ∣ n then F (n / p) else 0

/-- `towerQuot a = a + towerQuot a (·/p)`: the recursion of the tower quotient. -/
theorem towerQuot_eq_add (a : ℕ → ℂ) {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    towerQuot a p m = a m + if p ∣ m then towerQuot a p (m / p) else 0 := by
  rw [towerQuot_sub a hp hm]; ring

theorem towerQuot_zero (a : ℕ → ℂ) (p : ℕ) : towerQuot a p 0 = a 0 := by
  simp [towerQuot]

/-- **The tower quotient inverts the Euler factor.** -/
theorem towerQuot_eulerMul {F : ℕ → ℂ} {p : ℕ} (hp : p.Prime) (hF : F 0 = 0) (m : ℕ) :
    towerQuot (eulerMul p F) p m = F m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [towerQuot_zero, eulerMul, if_pos rfl, hF]
    rw [towerQuot_eq_add _ hp hm.ne', eulerMul, if_neg hm.ne']
    split_ifs with hpm
    · rw [ih (m / p) (Nat.div_lt_self hm hp.one_lt)]; ring
    · ring

/-- **The Euler factor inverts the tower quotient.** -/
theorem eulerMul_towerQuot {a : ℕ → ℂ} {p : ℕ} (hp : p.Prime) (ha : a 0 = 0) (n : ℕ) :
    eulerMul p (towerQuot a p) n = a n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [eulerMul, if_pos rfl, ha]
  · rw [eulerMul, if_neg hn.ne', towerQuot_sub a hp hn.ne']

/-- `towerQuot` as a linear map. -/
def towerQuotLin (p : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun a := towerQuot a p
  map_add' a b := by funext m; simp [towerQuot, Finset.sum_add_distrib]
  map_smul' c a := by funext m; simp [towerQuot, Finset.mul_sum]

/-- `eulerMul` as a linear map. -/
def eulerMulLin (p : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun := eulerMul p
  map_add' F G := by
    funext n; simp only [eulerMul, Pi.add_apply]; split_ifs <;> ring
  map_smul' c F := by
    funext n; simp only [eulerMul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- Multiplying a section of length `N/p` by the Euler factor gives a section of length `N`,
vanishing one order more along `p` and to the same orders along every other prime. -/
theorem eulerMul_mem_sections {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {N p k : ℕ} (hpS : p ∈ S)
    {m : ℕ → ℕ} (hm : m p = k + 1) {F : ℕ → ℂ}
    (hF : F ∈ sections (N / p) S (Function.update m p k)) : eulerMul p F ∈ sections N S m := by
  have hp := hS p hpS
  obtain ⟨hF00, hF0, hFv⟩ := hF
  have ha : ∀ n, n ≠ 0 → eulerMul p F n = F n - if p ∣ n then F (n / p) else 0 := fun n hn => by
    rw [eulerMul, if_neg hn]
  refine ⟨by rw [eulerMul, if_pos rfl], fun n hn => ?_, fun q hq => ?_⟩
  · rw [ha n (by omega), hF0 n (lt_of_le_of_lt (Nat.div_le_self N p) hn)]
    split_ifs with hpn
    · have : N / p < n / p := by
        obtain ⟨c, rfl⟩ := hpn
        rw [Nat.mul_div_cancel_left _ hp.pos]
        by_contra hc
        push Not at hc
        have := Nat.mul_le_mul_left p hc
        have := Nat.mul_div_le N p
        omega
      rw [hF0 _ this]; ring
    · ring
  have hid := fun i s => dirDeriv_quot (a := eulerMul p F) hp ha hF0 i s
  by_cases hqp : q = p
  · subst hqp
    have hFp := hFv q hpS
    rw [Function.update_self] at hFp
    intro i hi
    have hall : ∀ᶠ j in (cofinite : Filter ℤ), ∀ l ∈ range k,
        dirDeriv F (N / q) l (frobPoint q j) = 0 :=
      (Filter.eventually_all_finset _).mpr fun l hl => hFp l (Finset.mem_range.mp hl)
    filter_upwards [hall] with j hj
    rw [hid, cpow_neg_frobPoint_self hp, one_mul, Finset.sum_range_succ, Nat.choose_self,
      Nat.sub_self, pow_zero, Finset.sum_eq_zero fun l hl => by
        rw [hj l (Finset.mem_range.mpr (by have := Finset.mem_range.mp hl; omega)), mul_zero]]
    simp
  · have hFq := hFv q hq
    rw [Function.update_of_ne hqp] at hFq
    intro i hi
    have hall : ∀ᶠ j in (cofinite : Filter ℤ), ∀ l ∈ range (m q),
        dirDeriv F (N / p) l (frobPoint q j) = 0 :=
      (Filter.eventually_all_finset _).mpr fun l hl => hFq l (Finset.mem_range.mp hl)
    filter_upwards [hall] with j hj
    rw [hid, hj i (Finset.mem_range.mpr hi), Finset.sum_eq_zero fun l hl => by
      rw [hj l (Finset.mem_range.mpr (by have := Finset.mem_range.mp hl; omega)), mul_zero]]
    ring

/-- The tower quotient of a section of length `N` vanishing along `p` is a section of length `N/p`
with divisor lowered by one at `p`. -/
theorem towerQuot_mem_sections {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {N p k : ℕ} (hpS : p ∈ S)
    {m : ℕ → ℕ} (hm : m p = k + 1) {a : ℕ → ℂ} (ha : a ∈ sections N S m) :
    towerQuot a p ∈ sections (N / p) S (Function.update m p k) := by
  have hp := hS p hpS
  obtain ⟨ha00, ha0, hav⟩ := ha
  obtain ⟨hF0, hFp, hFq⟩ := towerQuot_vanishes hp ha0 (hm ▸ hav p hpS)
  refine ⟨by rw [towerQuot_zero, ha00], hF0, fun q hq => ?_⟩
  by_cases hqp : q = p
  · subst hqp; rw [Function.update_self]; exact hFp
  · rw [Function.update_of_ne hqp]; exact hFq q (hS q hq) hqp _ (hav q hq)

/-- **One division step is an isomorphism**: sections of length `N` with divisor `m` are, through
the Euler factor `1 − p^{−s}`, the sections of length `⌊N/p⌋` with divisor `m − e_p`. -/
def sectionsEquivQuot {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {N p k : ℕ} (hpS : p ∈ S)
    {m : ℕ → ℕ} (hm : m p = k + 1) :
    sections N S m ≃ₗ[ℂ] sections (N / p) S (Function.update m p k) :=
  LinearEquiv.ofLinear
    ((towerQuotLin p).restrict fun _ ha => towerQuot_mem_sections hS hpS hm ha)
    ((eulerMulLin p).restrict fun _ hF => eulerMul_mem_sections hS hpS hm hF)
    (LinearMap.ext fun F => Subtype.ext (funext fun n =>
      towerQuot_eulerMul (hS p hpS) F.2.1 n))
    (LinearMap.ext fun a => Subtype.ext (funext fun n =>
      eulerMul_towerQuot (hS p hpS) a.2.1 n))

/-! ### Riemann–Roch -/

/-- **The Riemann–Roch theorem of `𝔾_m(ℚ)`**: the sections of length `N` vanishing to order `m_p`
along the Frobenius progression of every `p ∈ S` form a space of dimension `⌊N/∏ p^{m_p}⌋`. -/
theorem finrank_sections {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∀ (k : ℕ) (m : ℕ → ℕ) (N : ℕ), ∑ p ∈ S, m p ≤ k →
      Module.finrank ℂ (sections N S m) = N / ∏ p ∈ S, p ^ m p := by
  classical
  intro k
  induction k with
  | zero =>
    intro m N hk
    have hm0 : ∀ p ∈ S, m p = 0 := fun p hp =>
      Nat.eq_zero_of_le_zero ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp).trans hk)
    rw [sections_eq_dirPolys hm0, finrank_dirPolys,
      Finset.prod_eq_one fun p hp => by rw [hm0 p hp, pow_zero], Nat.div_one]
  | succ k ih =>
    intro m N hk
    by_cases hall : ∀ p ∈ S, m p = 0
    · rw [sections_eq_dirPolys hall, finrank_dirPolys,
        Finset.prod_eq_one fun p hp => by rw [hall p hp, pow_zero], Nat.div_one]
    push Not at hall
    obtain ⟨p, hpS, hmp⟩ := hall
    obtain ⟨mp, hmp'⟩ : ∃ mp, m p = mp + 1 := ⟨m p - 1, by omega⟩
    have hsum : ∑ q ∈ S, Function.update m p mp q + 1 = ∑ q ∈ S, m q := by
      rw [← Finset.add_sum_erase _ _ hpS, ← Finset.add_sum_erase _ _ hpS,
        Function.update_self, hmp',
        Finset.sum_congr rfl fun q hq => Function.update_of_ne (Finset.ne_of_mem_erase hq) _ _]
      ring
    have hprod : ∏ q ∈ S, q ^ m q = p * ∏ q ∈ S, q ^ Function.update m p mp q := by
      have h' : ∏ q ∈ S.erase p, q ^ Function.update m p mp q = ∏ q ∈ S.erase p, q ^ m q :=
        Finset.prod_congr rfl fun q hq => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hq)]
      rw [← Finset.mul_prod_erase _ _ hpS, ← Finset.mul_prod_erase _ _ hpS, h',
        Function.update_self, hmp', pow_succ]
      ring
    rw [(sectionsEquivQuot hS hpS hmp').finrank_eq, ih _ _ (by omega), hprod,
      Nat.div_div_eq_div_mul]

/-- `h⁰(N, m) = ⌊N/∏ p^{m_p}⌋`. -/
theorem finrank_sections_eq {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (m : ℕ → ℕ) (N : ℕ) :
    Module.finrank ℂ (sections N S m) = N / ∏ p ∈ S, p ^ m p :=
  finrank_sections hS _ m N le_rfl

/-- **Bézout with its converse**: a nonzero section exists iff `∏ p^{m_p} ≤ N`. -/
theorem sections_ne_bot_iff {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (m : ℕ → ℕ) (N : ℕ) :
    sections N S m ≠ ⊥ ↔ ∏ p ∈ S, p ^ m p ≤ N := by
  have hpos : 0 < ∏ p ∈ S, p ^ m p := Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _
  rw [Ne, ← Submodule.finrank_eq_zero, finrank_sections_eq hS, Nat.div_eq_zero_iff_lt hpos,
    not_lt]

/-! ### Calibration over `𝔽_q[T]` -/

section Calibration

open Polynomial

/-- The polynomials of degree `< n` divisible by `Q`. -/
def divisibleLT (Q : ℂ[X]) (n : ℕ) : Submodule ℂ ℂ[X] :=
  degreeLT ℂ n ⊓ (Ideal.span {Q}).restrictScalars ℂ

/-- **Divisibility costs the degree of the divisor**: for monic `Q` of degree `k ≤ n`, the
polynomials of degree `< n` divisible by `Q` form a space of dimension `n − k`. -/
theorem finrank_divisibleLT {Q : ℂ[X]} (hQ : Q.Monic) {n : ℕ} (hk : Q.natDegree ≤ n) :
    Module.finrank ℂ (divisibleLT Q n) = n - Q.natDegree := by
  set k := Q.natDegree
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hdeg : ∀ R : ℂ[X], R ∈ degreeLT ℂ (n - k) ↔ Q * R ∈ degreeLT ℂ n := fun R => by
    rw [mem_degreeLT, mem_degreeLT]
    by_cases hR0 : R = 0
    · simp only [hR0, mul_zero, degree_zero]
      exact ⟨fun _ => WithBot.bot_lt_coe n, fun _ => WithBot.bot_lt_coe _⟩
    have hQR : Q * R ≠ 0 := mul_ne_zero hQ0 hR0
    rw [← natDegree_lt_iff_degree_lt hR0, ← natDegree_lt_iff_degree_lt hQR,
      natDegree_mul hQ0 hR0]
    omega
  let f : degreeLT ℂ (n - k) →ₗ[ℂ] divisibleLT Q n :=
    { toFun := fun R => ⟨Q * R, Submodule.mem_inf.mpr ⟨(hdeg R).mp R.2,
        (Submodule.restrictScalars_mem ℂ _ _).mpr
          (Ideal.mem_span_singleton.mpr (dvd_mul_right Q R))⟩⟩
      map_add' := fun R R' => Subtype.ext (mul_add Q R R')
      map_smul' := fun c R => Subtype.ext (mul_smul_comm c Q R) }
  have hbij : Function.Bijective f := by
    refine ⟨fun R R' h => Subtype.ext (mul_left_cancel₀ hQ0 (congrArg Subtype.val h)),
      fun P => ?_⟩
    obtain ⟨hPn, hPQ⟩ := Submodule.mem_inf.mp P.2
    obtain ⟨R, hR⟩ := Ideal.mem_span_singleton.mp ((Submodule.restrictScalars_mem ℂ _ _).mp hPQ)
    refine ⟨⟨R, (hdeg R).mpr (by rw [← hR]; exact hPn)⟩, Subtype.ext ?_⟩
    exact hR.symm
  rw [← (LinearEquiv.ofBijective f hbij).finrank_eq, (degreeLTEquiv ℂ (n - k)).finrank_eq,
    Module.finrank_fin_fun]

/-- **The additive Riemann–Roch over `𝔽_q[T]`.** With `u = q^{−s}`, a Dirichlet polynomial over
`𝔽_q[T]` of length `q^d` is a polynomial of degree `≤ d` in `u`, and the Euler factor of a place
of degree `e` is `1 − u^e`. The polynomials divisible by `(u^e − 1)^m` form a space of dimension
`d + 1 − em`: vanishing to order `m` along the progression of a place of degree `e` costs `em`
conditions, the same for every place of that degree, because they share the progression. Over `ℤ`
the cost is multiplicative: `h⁰ = ⌊N/p^m⌋` (`finrank_sections_eq`). -/
theorem finrank_divisibleLT_eulerFactor {e m d : ℕ} (he : 0 < e) (hd : e * m ≤ d + 1) :
    Module.finrank ℂ (divisibleLT ((X ^ e - C 1) ^ m) (d + 1)) = d + 1 - e * m := by
  have hmon : ((X ^ e - C 1 : ℂ[X]) ^ m).Monic := (monic_X_pow_sub_C 1 he.ne').pow m
  have hdeg : ((X ^ e - C 1 : ℂ[X]) ^ m).natDegree = e * m := by
    rw [natDegree_pow, natDegree_X_pow_sub_C, mul_comm]
  rw [finrank_divisibleLT hmon (by rw [hdeg]; exact hd), hdeg]

end Calibration

end GaloisForLFunctions.EffectiveArithmeticHodgeTheory
