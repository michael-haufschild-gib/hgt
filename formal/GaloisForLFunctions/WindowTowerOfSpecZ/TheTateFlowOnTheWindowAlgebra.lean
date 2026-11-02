import GaloisForLFunctions.WindowTowerOfSpecZ.TheWindowFormIsTheDerivativeOfTheJordanCounts
import GaloisForLFunctions.WindowTowerOfSpecZ.TheTowerOfSmallExtensions

/-!
# The Tate flow on the window algebra

The Tate twists `f ↦ f·n^{−c}` are ring automorphisms of the Dirichlet ring (`tateTwistHom`), a
one-parameter group (`tateTwist_tateTwist`), implemented on every window by conjugation with
`e^{cu}` (`windowRepFun_twist`). Their generator is the degree derivation, i.e. the commutator with
the position.

For an **Euler datum** `(F, G)` with `F * G = 1` the **Tate family** `J^F_k = (twist by −k of F) * G`
(`tateFamily`) measures how far the flow moves `F`:

* **It is a cocycle of the Tate flow** (`tateFamily_add`): `J^F_{k+l} = twist_{−k}(J^F_l) * J^F_k`,
  `J^F_0 = 1`. For `ζ` it is the Jordan family (`tateFamily_zeta`).
* **On a window it is a group commutator** (`windowRepFun_jordan_eq_commutator`):
  `ρ_A(J_k) = e^{kM} Z e^{−kM} Z^{−1}`, `Z = ρ_A(ζ)`. The Tate pieces of the degeneration are the
  commutators of the window zeta operator with the Tate flow at integer times; Weil's arithmetic
  operator `ρ_A(Λ) = [M, Z]Z^{−1}` is the infinitesimal commutator.
* **Conjugation form** (`windowRep_zeta_conj_position`): `Z M Z^{−1} = M − ρ_A(Λ)`.
* **Hensel tower** (`jordanTotient_prime_pow_succ`, `hasDerivAt_jordanTotient_prime_pow`): along the
  powers of `p` the Tate pieces grow by the fibre count `p^k` of reduction `(ℤ/p^{a+1})^k → (ℤ/p^a)^k`,
  while the non-Tate piece stays `log p`.
* **Tate pieces at a prime have the sign of the weight** (`tateFamily_prime`,
  `logDeriv_prime`): `J^F_k(p) = F(p)(p^k − 1)` and the logarithmic-derivative weight is
  `λ_F(p) = F(p) log p`. A flip of the sign of `Λ` at `p` (a flip twin) makes every Tate piece at
  `p` negative (`flipDatum_tateFamily_prime_neg`), at the stage `p` where the flip becomes visible.
* **Tate positivity is soft** (`shiftedDatum_tateFamily_nonneg`): the shifted datum
  `F_ε = ζ * twist_{−ε}ζ` (the Dirichlet series `ζ(s)ζ(s − ε)`, whose zeros `ρ + ε` leave the critical
  line for `ε > 0`) has nonnegative Tate pieces in every positive dimension. Counts at integer
  dimensions cannot select `ζ`; selection lives in the derivative at dimension zero against the
  archimedean data, i.e. in Weil's form along the whole tower.
-/

noncomputable section

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ ArithmeticDegenerationTheory

/-! ### The Tate flow -/

theorem tateTwist_mul (c : ℝ) (f g : ArithmeticFunction ℝ) :
    tateTwist c (f * g) = tateTwist c f * tateTwist c g := by
  ext n
  rw [tateTwist_apply, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨hxn, _⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  rw [tateTwist_apply, tateTwist_apply, ← hxn, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

theorem tateTwist_one (c : ℝ) : tateTwist c (1 : ArithmeticFunction ℝ) = 1 := by
  ext n
  rw [tateTwist_apply, ArithmeticFunction.one_apply]
  split_ifs with h
  · rw [h, Nat.cast_one, Real.one_rpow, mul_one]
  · rw [zero_mul]

/-- The Tate twist by `c` as a ring automorphism of the Dirichlet ring. -/
def tateTwistHom (c : ℝ) : ArithmeticFunction ℝ →+* ArithmeticFunction ℝ where
  toFun := tateTwist c
  map_one' := tateTwist_one c
  map_mul' := tateTwist_mul c
  map_zero' := by ext n; simp [tateTwist_apply]
  map_add' f g := by ext n; simp [tateTwist_apply, add_mul]

theorem tateTwist_tateTwist (a b : ℝ) (f : ArithmeticFunction ℝ) :
    tateTwist a (tateTwist b f) = tateTwist (a + b) f := by
  ext n
  rw [tateTwist_apply, tateTwist_apply, tateTwist_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [mul_assoc, ← Real.rpow_add (by exact_mod_cast hn)]
    ring_nf

theorem tateTwist_zero (f : ArithmeticFunction ℝ) : tateTwist 0 f = f := by
  ext n; rw [tateTwist_apply, neg_zero, Real.rpow_zero, mul_one]

/-! ### Euler data and their Tate families -/

/-- The **Tate family** `J^F_k = twist_{−k}(F) * G` of an Euler datum. -/
def tateFamily (F G : ArithmeticFunction ℝ) (k : ℝ) : ArithmeticFunction ℝ :=
  tateTwist (-k) F * G

theorem tateFamily_zero {F G : ArithmeticFunction ℝ} (hFG : F * G = 1) : tateFamily F G 0 = 1 := by
  rw [tateFamily, neg_zero, tateTwist_zero, hFG]

/-- **The Tate family is a cocycle of the Tate flow**: `J^F_{k+l} = twist_{−k}(J^F_l) * J^F_k`. -/
theorem tateFamily_add {F G : ArithmeticFunction ℝ} (hFG : F * G = 1) (k l : ℝ) :
    tateFamily F G (k + l) = tateTwist (-k) (tateFamily F G l) * tateFamily F G k := by
  have hGF : tateTwist (-k) G * tateTwist (-k) F = 1 := by
    rw [← tateTwist_mul, mul_comm, hFG, tateTwist_one]
  rw [tateFamily, tateFamily, tateFamily, tateTwist_mul, tateTwist_tateTwist,
    show -k + -l = -(k + l) by ring]
  calc tateTwist (-(k + l)) F * G
      = tateTwist (-(k + l)) F * (tateTwist (-k) G * tateTwist (-k) F) * G := by
        rw [hGF, mul_one]
    _ = tateTwist (-(k + l)) F * tateTwist (-k) G * (tateTwist (-k) F * G) := by ring

/-- For `ζ` the Tate family is the Jordan family. -/
theorem tateFamily_zeta (k : ℝ) :
    tateFamily (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) k = jordanFun k :=
  (jordanFun_eq k).symm

/-! ### The Tate operators are group commutators -/

/-- **The Tate operator is a group commutator**: `ρ_A(J_k) H = e^{ku} · ρ_A(ζ)(e^{−kv} ρ_A(μ)H)`,
i.e. `ρ_A(J_k) = e^{kM} Z e^{−kM} Z^{−1}` with `Z = ρ_A(ζ)`. -/
theorem windowRepFun_jordan_eq_commutator {A : ℝ} {H : ℝ → ℝ} (hH : H ∈ windowSupported A)
    (k u : ℝ) :
    windowRepFun A (jordanFun k) H u = Real.exp (k * u) *
      windowRepFun A (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
        (fun v => Real.exp (-k * v) *
          windowRepFun A (ArithmeticFunction.moebius : ArithmeticFunction ℝ) H v) u := by
  rw [windowRepFun_twist, ← mul_assoc, ← Real.exp_add, show k * u + -k * u = 0 by ring,
    Real.exp_zero, one_mul, jordanFun_eq, ← windowRepFun_mul _ _ hH]

/-- **The window zeta operator conjugates the position into position minus von Mangoldt**:
`Z M Z^{−1} = M − ρ_A(Λ)`, the operator form of the logarithmic derivative `−ζ′/ζ = Σ Λ(n)n^{−s}`. -/
theorem windowRep_zeta_conj_position (A : ℝ) :
    windowRep A (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * positionOp A *
        windowRep A (ArithmeticFunction.moebius : ArithmeticFunction ℝ) =
      positionOp A - windowRep A ArithmeticFunction.vonMangoldt := by
  set Z := windowRep A (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  set Zi := windowRep A (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
  set L := windowRep A ArithmeticFunction.vonMangoldt
  set M := positionOp A
  have h1 : M * Z - Z * M = windowRep A ArithmeticFunction.log := by
    rw [position_comm_windowRep, pmul_zeta_log]
  have h2 : L * Z = windowRep A ArithmeticFunction.log := by
    rw [← map_mul, ArithmeticFunction.vonMangoldt_mul_zeta]
  have h3 : Z * Zi = 1 := windowRep_zeta_mul_moebius A
  refine LinearMap.ext fun H => ?_
  have e1 := congrArg (fun φ : Module.End ℝ (windowSupported A) => φ (Zi H)) h1
  have e2 := congrArg (fun φ : Module.End ℝ (windowSupported A) => φ (Zi H)) h2
  have e3 := congrArg (fun φ : Module.End ℝ (windowSupported A) => φ H) h3
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply] at e1 e2 e3 ⊢
  rw [e3] at e1 e2
  rw [← e2] at e1
  rw [← e1]
  abel

/-! ### The Hensel tower of Tate pieces -/

/-- **Hensel tower**: along the powers of a prime the Tate pieces grow by the fibre count `p^k`,
`J_k(p^{a+1}) = p^k J_k(p^a)` (`a ≥ 1`), while the non-Tate piece `∂_kJ_k(p^a)|₀ = log p` is the same
at every stage (`hasDerivAt_jordanTotient_prime_pow`). -/
theorem jordanTotient_prime_pow_succ {p : ℕ} (hp : p.Prime) (k : ℝ) {a : ℕ} (ha : 1 ≤ a) :
    jordanTotient k (p ^ (a + 1)) = (p : ℝ) ^ k * jordanTotient k (p ^ a) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [jordanTotient_prime_pow hp k (by omega), jordanTotient_prime_pow hp k ha,
    show (a + 1 - 1 : ℕ) = (a - 1) + 1 by omega, Nat.cast_add, Nat.cast_one, mul_add, mul_one,
    Real.rpow_add hp0]
  ring

theorem hasDerivAt_jordanTotient_prime_pow {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 1 ≤ a) :
    HasDerivAt (fun k => jordanTotient k (p ^ a)) (Real.log p) 0 := by
  have h := hasDerivAt_jordanTotient_zero (p ^ a)
  rwa [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime hp] at h

/-! ### Tate pieces at a prime -/

theorem mul_apply_prime {p : ℕ} (hp : p.Prime) (f g : ArithmeticFunction ℝ) :
    (f * g) p = f 1 * g p + f p * g 1 := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b),
    Nat.Prime.divisors hp, Finset.sum_insert (by rw [Finset.mem_singleton]; exact hp.one_lt.ne),
    Finset.sum_singleton,
    Nat.div_one, Nat.div_self hp.pos]

theorem inverse_prime {F G : ArithmeticFunction ℝ} (hFG : F * G = 1) (hF1 : F 1 = 1) {p : ℕ}
    (hp : p.Prime) : G 1 = 1 ∧ G p = -F p := by
  have h1 : (F * G) 1 = 1 := by rw [hFG, ArithmeticFunction.one_one]
  rw [ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_one, Finset.sum_singleton, hF1,
    one_mul] at h1
  have hp1 : (F * G) p = 0 := by rw [hFG, ArithmeticFunction.one_apply_ne hp.one_lt.ne']
  rw [mul_apply_prime hp, hF1, h1, one_mul, mul_one] at hp1
  exact ⟨h1, by linarith⟩

/-- **The Tate piece at a prime**: `J^F_k(p) = F(p)(p^k − 1)`. -/
theorem tateFamily_prime {F G : ArithmeticFunction ℝ} (hFG : F * G = 1) (hF1 : F 1 = 1) {p : ℕ}
    (hp : p.Prime) (k : ℝ) : tateFamily F G k p = F p * ((p : ℝ) ^ k - 1) := by
  obtain ⟨hG1, hGp⟩ := inverse_prime hFG hF1 hp
  rw [tateFamily, mul_apply_prime hp, tateTwist_apply, tateTwist_apply, hF1, hG1, hGp, neg_neg]
  simp
  ring

/-- **The logarithmic-derivative weight at a prime** is `λ_F(p) = F(p) log p`. -/
theorem logDeriv_prime {F G : ArithmeticFunction ℝ} (hFG : F * G = 1) (hF1 : F 1 = 1) {p : ℕ}
    (hp : p.Prime) : (F.pmul ArithmeticFunction.log * G) p = F p * Real.log p := by
  obtain ⟨hG1, _⟩ := inverse_prime hFG hF1 hp
  rw [mul_apply_prime hp, ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.log_apply, ArithmeticFunction.log_apply, Nat.cast_one, Real.log_one, hG1]
  ring

/-- **Tate pieces at a prime have the sign of the weight**:
`J^F_k(p) · log p = λ_F(p) (p^k − 1)`. -/
theorem tateFamily_prime_mul_log {F G : ArithmeticFunction ℝ} (hFG : F * G = 1) (hF1 : F 1 = 1)
    {p : ℕ} (hp : p.Prime) (k : ℝ) :
    tateFamily F G k p * Real.log p = (F.pmul ArithmeticFunction.log * G) p * ((p : ℝ) ^ k - 1) := by
  rw [tateFamily_prime hFG hF1 hp, logDeriv_prime hFG hF1 hp]
  ring

/-! ### Flip twins violate Tate positivity -/

/-- The Euler datum of a prime flip, `F_p = ζ * (1 − δ_p)²`: the Dirichlet series
`ζ(s)(1 − p^{−s})²`, whose logarithmic derivative is `Λ` with the sign flipped on the powers of `p`. -/
def flipDatum (p : ℕ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * ((1 - single p 1) * (1 - single p 1))

theorem flipDatum_one {p : ℕ} (hp : p.Prime) : flipDatum p 1 = 1 := by
  rw [flipDatum, ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_one, Finset.sum_singleton,
    ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_one, Finset.sum_singleton]
  simp [sub_apply', single_apply, hp.one_lt.ne]

theorem flipDatum_prime {p : ℕ} (hp : p.Prime) : flipDatum p p = -1 := by
  have hsub : ∀ q : ℕ, (1 - single p (1 : ℝ)) q = (if q = 1 then 1 else 0) -
      (if q = p ∧ q ≠ 0 then 1 else 0) := fun q => by
    rw [sub_apply', ArithmeticFunction.one_apply, single_apply]
  rw [flipDatum, mul_apply_prime hp, mul_apply_prime hp, ArithmeticFunction.mul_apply,
    Nat.divisorsAntidiagonal_one, Finset.sum_singleton]
  simp only [hsub]
  simp [hp.one_lt.ne, hp.one_lt.ne', hp.ne_zero, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply]

/-- **Flip twins violate Tate positivity**: for any inverse `G` of the flip datum at `p`, every Tate
piece at `p` in positive dimension is negative, `J^{F_p}_k(p) = −(p^k − 1) < 0`. -/
theorem flipDatum_tateFamily_prime_neg {p : ℕ} (hp : p.Prime) {G : ArithmeticFunction ℝ}
    (hG : flipDatum p * G = 1) {k : ℝ} (hk : 0 < k) : tateFamily (flipDatum p) G k p < 0 := by
  rw [tateFamily_prime hG (flipDatum_one hp) hp, flipDatum_prime hp]
  have : 1 < (p : ℝ) ^ k := Real.one_lt_rpow (by exact_mod_cast hp.one_lt) hk
  linarith

/-! ### Tate positivity is soft -/

theorem tateTwist_nonneg {c : ℝ} {f : ArithmeticFunction ℝ} (hf : ∀ n, 0 ≤ f n) (n : ℕ) :
    0 ≤ tateTwist c f n := by
  rw [tateTwist_apply]
  exact mul_nonneg (hf n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem mul_nonneg_af {f g : ArithmeticFunction ℝ} (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n)
    (n : ℕ) : 0 ≤ (f * g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hf _) (hg _)

theorem jordanFun_succ_nonneg (β : ℕ) (n : ℕ) : 0 ≤ jordanFun (β + 1 : ℕ) n :=
  jordanTotient_succ_nonneg β n

/-- The shifted Euler datum `F_ε = ζ * twist_{−ε}ζ`, the Dirichlet series `ζ(s)ζ(s − ε)`, and its
inverse `G_ε = μ * twist_{−ε}μ`. -/
def shiftedDatum (ε : ℝ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
    tateTwist (-ε) (ArithmeticFunction.zeta : ArithmeticFunction ℝ)

def shiftedInverse (ε : ℝ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
    tateTwist (-ε) (ArithmeticFunction.moebius : ArithmeticFunction ℝ)

theorem shiftedDatum_mul_inverse (ε : ℝ) : shiftedDatum ε * shiftedInverse ε = 1 := by
  have h := ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ)
  have h' : tateTwist (-ε) (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      tateTwist (-ε) (ArithmeticFunction.moebius : ArithmeticFunction ℝ) = 1 := by
    rw [← tateTwist_mul, h, tateTwist_one]
  calc shiftedDatum ε * shiftedInverse ε
      = ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) *
        (tateTwist (-ε) (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          tateTwist (-ε) (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) := by
        rw [shiftedDatum, shiftedInverse]; ring
    _ = 1 := by rw [h, h', one_mul]

/-- The Tate family of the shifted datum factors: `J^{F_ε}_k = J_k * twist_{−ε}(J_k)`. -/
theorem tateFamily_shiftedDatum (ε k : ℝ) :
    tateFamily (shiftedDatum ε) (shiftedInverse ε) k = jordanFun k * tateTwist (-ε) (jordanFun k) := by
  rw [tateFamily, shiftedDatum, shiftedInverse, jordanFun_eq, tateTwist_mul, tateTwist_mul,
    tateTwist_tateTwist, tateTwist_tateTwist, show -k + -ε = -ε + -k by ring]
  ring

/-- **Tate positivity is soft**: the shifted datum `ζ(s)ζ(s − ε)` has nonnegative Tate pieces in every
positive integer dimension. -/
theorem shiftedDatum_tateFamily_nonneg (ε : ℝ) (β : ℕ) (n : ℕ) :
    0 ≤ tateFamily (shiftedDatum ε) (shiftedInverse ε) (β + 1 : ℕ) n := by
  rw [tateFamily_shiftedDatum]
  exact mul_nonneg_af (jordanFun_succ_nonneg β) (tateTwist_nonneg (jordanFun_succ_nonneg β)) n

end GaloisForLFunctions.WindowTowerOfSpecZ
