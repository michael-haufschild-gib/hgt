import GaloisForLFunctions.RHTower.XiDeckCharge
import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.ExponentialSumDA

/-!
# The deck charge is a divisor invariant — and is blind to the differential-algebraic class

The ξ deck charge `xiDeckCharge k ρ = exp(2πi·ord_ρ(ξ)/2^k)` is here generalized to a **deck charge of
an arbitrary function**, `deckCharge f k ρ = exp(2πi·ord_ρ(f)/2^k)`, the monodromy of the
`2^k`-th-root torsor of `f` around `ρ`.  This makes precise the status of the root-tower charge as a
*general* invariant, and locates exactly what it can and cannot see.

The charge carries the full dyadic-tower structure at every function (`deckCharge_pow`,
`deckCharge_succ_sq`, `deckCharge_eq_one_iff_toNat_dvd`, `deckCharge_eq_one_iff_le_val`), and
`xiDeckCharge = deckCharge xi` (`xiDeckCharge_eq_deckCharge`).  But it is read entirely off the
**vanishing order** — a non-negative integer — and therefore:

* it depends only on the divisor (`deckCharge_of_orderEq`);
* it is invariant under multiplication by any locally nonvanishing analytic factor
  (`deckCharge_mul_unit`);
* consequently it is **blind to the differential-algebraic class**: a nowhere-zero function has trivial
  charge whatever its analytic nature, so a hypertranscendental nowhere-zero function and the constant
  `1` (differentially algebraic) carry *identical* charge towers (`deckCharge_blind_to_class`).

So the conjectural dichotomy "differentially algebraic ⟺ eventually-periodic (rational) root-tower
charge, hypertranscendental ⟺ aperiodic charge" is **false**: the per-point charge tower is the
`2`-adic expansion of an ordinary integer (the multiplicity), hence eventually periodic for *every*
function — differentially algebraic or hypertranscendental.  What the charge genuinely computes is the
`2`-adic valuation of the local multiplicity (`deckCharge_eq_one_iff_le_val`): a real, computable
invariant of the **divisor**, provably orthogonal to the analytic class it was hoped to detect.  The
obstruction is located exactly — the charge is a discrete (order-theoretic) datum, and
hypertranscendence is a differential one it cannot reach.
-/

open Complex

namespace RHTower

/-! ### §1 The deck charge of an arbitrary function, and its dyadic-tower structure -/

/-- **General deck charge.**  The level-`2^k` monodromy of the `2^k`-th-root torsor of `f` around `ρ`,
`exp(2πi·ord_ρ(f)/2^k)`.  Written from the vanishing order, so root-choice independent. -/
noncomputable def deckCharge (f : ℂ → ℂ) (k : ℕ) (ρ : ℂ) : ℂ :=
  exp (2 * (Real.pi : ℂ) * I * ((analyticOrderAt f ρ).toNat : ℕ) / ((2 ^ k : ℕ) : ℂ))

/-- The ξ deck charge is the general deck charge at `ξ`. -/
theorem xiDeckCharge_eq_deckCharge (k : ℕ) (ρ : ℂ) : xiDeckCharge k ρ = deckCharge xi k ρ := rfl

/-- **Triviality reads divisibility.**  The charge is `1` iff `2^k` divides the vanishing order. -/
theorem deckCharge_eq_one_iff_toNat_dvd (f : ℂ → ℂ) (k : ℕ) (ρ : ℂ) :
    deckCharge f k ρ = 1 ↔ 2 ^ k ∣ (analyticOrderAt f ρ).toNat := by
  unfold deckCharge
  exact exp_two_pi_mul_div_eq_one_iff (pow_pos (by norm_num) k) ((analyticOrderAt f ρ).toNat)

/-- The charge is a `2^k`-th root of unity: it takes values in `μ_{2^k}`. -/
theorem deckCharge_pow (f : ℂ → ℂ) (k : ℕ) (ρ : ℂ) : deckCharge f k ρ ^ (2 ^ k) = 1 := by
  unfold deckCharge
  rw [← exp_nat_mul]
  have h2k : ((2 ^ k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos (by norm_num) k).ne'
  have harg : ((2 ^ k : ℕ) : ℂ) *
      (2 * (Real.pi : ℂ) * I * ((analyticOrderAt f ρ).toNat : ℕ) / ((2 ^ k : ℕ) : ℂ))
      = ((analyticOrderAt f ρ).toNat : ℕ) * (2 * (Real.pi : ℂ) * I) := by field_simp
  rw [harg, exp_nat_mul, exp_two_pi_mul_I, one_pow]

/-- **Dyadic coherence.**  Squaring the level-`k+1` charge gives the level-`k` charge:
`w_{k+1}² = w_k`.  This is the tower structure of the deck classes at every function. -/
theorem deckCharge_succ_sq (f : ℂ → ℂ) (k : ℕ) (ρ : ℂ) :
    deckCharge f (k + 1) ρ ^ 2 = deckCharge f k ρ := by
  unfold deckCharge
  rw [← exp_nat_mul]
  congr 1
  have h2k : ((2 ^ k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos (by norm_num) k).ne'
  have e : ((2 ^ (k + 1) : ℕ) : ℂ) = ((2 : ℕ) : ℂ) * ((2 ^ k : ℕ) : ℂ) := by push_cast; ring
  rw [e]; field_simp

/-- Off the divisor the charge is trivial: a non-zero has order `0`, divisible by all `2^k`. -/
theorem deckCharge_eq_one_of_ne_zero (f : ℂ → ℂ) (k : ℕ) {ρ : ℂ} (h : f ρ ≠ 0) :
    deckCharge f k ρ = 1 := by
  rw [deckCharge_eq_one_iff_toNat_dvd]
  rw [analyticOrderAt_eq_zero.mpr (Or.inr h)]; simp

/-- **The whole charge tower is trivial iff `f` does not vanish.**  At an analytic point of finite
order, the level-`k` charge is `1` for every `k` iff `f ρ ≠ 0`: a positive finite order cannot be
divisible by every `2^k`. -/
theorem forall_deckCharge_eq_one_iff (f : ℂ → ℂ) (ρ : ℂ)
    (hana : AnalyticAt ℂ f ρ) (hfin : analyticOrderAt f ρ ≠ ⊤) :
    (∀ k, deckCharge f k ρ = 1) ↔ f ρ ≠ 0 := by
  constructor
  · intro h hz
    have hdvd : ∀ k, 2 ^ k ∣ (analyticOrderAt f ρ).toNat := fun k =>
      (deckCharge_eq_one_iff_toNat_dvd f k ρ).mp (h k)
    have horder_ne : analyticOrderAt f ρ ≠ 0 := by
      intro hcon
      rcases analyticOrderAt_eq_zero.mp hcon with hh | hh
      · exact hh hana
      · exact hh hz
    have hne : (analyticOrderAt f ρ).toNat ≠ 0 := by
      intro hcon
      rcases ENat.toNat_eq_zero.mp hcon with hh | hh
      · exact horder_ne hh
      · exact hfin hh
    have h2 : 2 ^ (analyticOrderAt f ρ).toNat ≤ (analyticOrderAt f ρ).toNat :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (hdvd _)
    have h3 : (analyticOrderAt f ρ).toNat < 2 ^ (analyticOrderAt f ρ).toNat :=
      Nat.lt_pow_self (by norm_num)
    omega
  · intro h k; exact deckCharge_eq_one_of_ne_zero f k h

/-! ### §2 The charge is a divisor invariant -/

/-- **The charge depends only on the divisor.**  Equal vanishing orders give equal charges. -/
theorem deckCharge_of_orderEq {f g : ℂ → ℂ} {ρ : ℂ}
    (h : analyticOrderAt f ρ = analyticOrderAt g ρ) (k : ℕ) :
    deckCharge f k ρ = deckCharge g k ρ := by
  unfold deckCharge; rw [h]

/-- **Invariance under a locally nonvanishing factor.**  Multiplying `f` by an analytic `u` that does
not vanish at `ρ` leaves the charge unchanged — the charge sees only the divisor, not the nonvanishing
part.  (Additivity of the order plus `ord_ρ(u) = 0`.) -/
theorem deckCharge_mul_unit {f u : ℂ → ℂ} {ρ : ℂ} (k : ℕ)
    (hf : AnalyticAt ℂ f ρ) (hu : AnalyticAt ℂ u ρ) (hu0 : u ρ ≠ 0) :
    deckCharge (f * u) k ρ = deckCharge f k ρ := by
  apply deckCharge_of_orderEq
  rw [analyticOrderAt_mul hf hu, analyticOrderAt_eq_zero.mpr (Or.inr hu0), add_zero]

/-- **Multiplicativity.**  The charge of a product is the product of the charges (at analytic points of
finite order): the deck charge is a homomorphism from the local divisor monoid to `μ_{2^k}`.  This is
`deckClass_mul` for the general charge — additivity of the order under `exp`. -/
theorem deckCharge_mul {f g : ℂ → ℂ} {ρ : ℂ} (k : ℕ)
    (hf : AnalyticAt ℂ f ρ) (hg : AnalyticAt ℂ g ρ)
    (hfT : analyticOrderAt f ρ ≠ ⊤) (hgT : analyticOrderAt g ρ ≠ ⊤) :
    deckCharge (f * g) k ρ = deckCharge f k ρ * deckCharge g k ρ := by
  unfold deckCharge
  rw [← Complex.exp_add]
  congr 1
  rw [analyticOrderAt_mul hf hg, ENat.toNat_add hfT hgT]
  push_cast; ring

/-- The vanishing order of a finite product of analytic functions of finite order is finite. -/
theorem analyticOrderAt_prod_ne_top {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {ρ : ℂ}
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) ρ) (hfT : ∀ i ∈ s, analyticOrderAt (f i) ρ ≠ ⊤) :
    analyticOrderAt (∏ i ∈ s, f i) ρ ≠ ⊤ := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, analyticOrderAt_eq_zero.mpr (Or.inr (show (1 : ℂ → ℂ) ρ ≠ 0 by simp))]
    simp
  | @insert a t ha ih =>
    rw [Finset.prod_insert ha, analyticOrderAt_mul (hf a (Finset.mem_insert_self a t))
      (Finset.analyticAt_prod t (fun i hi => hf i (Finset.mem_insert_of_mem hi)))]
    exact WithTop.add_ne_top.mpr ⟨hfT a (Finset.mem_insert_self a t),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => hfT i (Finset.mem_insert_of_mem hi))⟩

/-- **Multiplicativity over a finite product.**  The charge of a finite product is the product of the
charges (at analytic points of finite order): `deckClass_prod` for the general charge. -/
theorem deckCharge_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {ρ : ℂ} (k : ℕ)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) ρ) (hfT : ∀ i ∈ s, analyticOrderAt (f i) ρ ≠ ⊤) :
    deckCharge (∏ i ∈ s, f i) k ρ = ∏ i ∈ s, deckCharge (f i) k ρ := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty]
    exact deckCharge_eq_one_of_ne_zero _ k (show (1 : ℂ → ℂ) ρ ≠ 0 by simp)
  | @insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      deckCharge_mul k (hf a (Finset.mem_insert_self a t))
        (Finset.analyticAt_prod t (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
        (hfT a (Finset.mem_insert_self a t))
        (analyticOrderAt_prod_ne_top t f (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => hfT i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => hfT i (Finset.mem_insert_of_mem hi))]

/-- **Germ (deformation) invariance.**  The charge depends only on the germ of `f` at `ρ`: functions
agreeing near `ρ` have equal charge.  This is the deformation invariance of the deck calculus at the
level of the general charge — a deformation that does not change the germ at `ρ` leaves the charge
fixed. -/
theorem deckCharge_congr {f g : ℂ → ℂ} {ρ : ℂ} (k : ℕ) (h : f =ᶠ[nhds ρ] g) :
    deckCharge f k ρ = deckCharge g k ρ := by
  unfold deckCharge; rw [analyticOrderAt_congr h]

/-- **Schwarz conjugation.**  For a differentiable function that is real on the real axis
(`f(z̄) = f(z)‾`), the charge is invariant under `ρ ↦ ρ̄`: conjugation is an order-preserving involution
of the divisor.  This is `deckClass_conj` for the general charge. -/
theorem deckCharge_conj {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)) (k : ℕ) (ρ : ℂ) :
    deckCharge f k ((starRingEnd ℂ) ρ) = deckCharge f k ρ := by
  have hFeq : (fun w => (starRingEnd ℂ) (f ((starRingEnd ℂ) w))) = f :=
    funext fun w => by rw [hreal w, Complex.conj_conj]
  have hcongr : analyticOrderAt (fun w => (starRingEnd ℂ) (f ((starRingEnd ℂ) w)))
      ((starRingEnd ℂ) ρ) = analyticOrderAt f ((starRingEnd ℂ) ρ) :=
    congrFun (congrArg analyticOrderAt hFeq) _
  have hkey : analyticOrderAt f ((starRingEnd ℂ) ρ) = analyticOrderAt f ρ :=
    hcongr.symm.trans (analyticOrderAt_conj_conj hf ρ)
  unfold deckCharge
  rw [hkey]

/-! ### §3 The charge is blind to the differential-algebraic class -/

/-- The constant `1` has trivial charge everywhere. -/
theorem deckCharge_one (k : ℕ) (ρ : ℂ) : deckCharge (fun _ => (1 : ℂ)) k ρ = 1 :=
  deckCharge_eq_one_of_ne_zero _ k one_ne_zero

/-- The exponential has trivial charge everywhere (it never vanishes). -/
theorem deckCharge_exp (k : ℕ) (ρ : ℂ) : deckCharge Complex.exp k ρ = 1 :=
  deckCharge_eq_one_of_ne_zero _ k (Complex.exp_ne_zero ρ)

/-- The constant `1` is differentially algebraic. -/
theorem differentiallyAlgebraic_one :
    GaloisForLFunctions.DifferentiallyAlgebraic (fun _ : ℂ => (1 : ℂ)) := by
  have h := GaloisForLFunctions.differentiallyAlgebraic_cexp_linear 0
  simpa using h

/-- **The deck charge is blind to hypertranscendence.**  Any nowhere-zero function has the trivial
charge tower, so a *hypertranscendental* nowhere-zero function `h` and the constant `1` (differentially
algebraic) carry identical charges at every level and point — yet lie in opposite analytic classes.
The root-tower charge therefore cannot witness the differential-algebraic / hypertranscendental split.
A nowhere-zero hypertranscendental function exists classically (the exponential of a hypertranscendental
function is nowhere zero and hypertranscendental); here it is the explicit hypothesis, isolating that
the charge's blindness is unconditional and the only classical input is the existence of the witness. -/
theorem deckCharge_blind_to_class (h : ℂ → ℂ) (hne : ∀ ρ, h ρ ≠ 0)
    (hHT : GaloisForLFunctions.Hypertranscendental h) :
    GaloisForLFunctions.DifferentiallyAlgebraic (fun _ : ℂ => (1 : ℂ))
      ∧ GaloisForLFunctions.Hypertranscendental h
      ∧ ∀ k ρ, deckCharge h k ρ = deckCharge (fun _ : ℂ => (1 : ℂ)) k ρ := by
  refine ⟨differentiallyAlgebraic_one, hHT, fun k ρ => ?_⟩
  rw [deckCharge_eq_one_of_ne_zero h k (hne ρ), deckCharge_one]

/-! ### §4 What the charge does compute: the `2`-adic valuation of the multiplicity -/

/-- **The charge reads the `2`-adic height of the multiplicity.**  At a point of positive finite order,
the level-`k` charge is trivial iff `k` is at most the `2`-adic valuation of the multiplicity.  So the
charge tower is exactly the `2`-adic expansion of the vanishing order — a computable invariant of the
divisor, and (being an ordinary integer's expansion) eventually periodic for every function. -/
theorem deckCharge_eq_one_iff_le_val (f : ℂ → ℂ) (k : ℕ) {ρ : ℂ}
    (hord : (analyticOrderAt f ρ).toNat ≠ 0) :
    deckCharge f k ρ = 1 ↔ k ≤ (analyticOrderAt f ρ).toNat.factorization 2 := by
  rw [deckCharge_eq_one_iff_toNat_dvd]
  exact Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hord

/-- **The whole charge tower is determined by one integer.**  If two points carry the same vanishing
multiplicity, their entire charge towers coincide.  The root-tower charge is thus *finite* data — a
single natural number — hence a rational point of the `2`-adic root torsor, "eventually periodic" in
the only sense available.  Because the multiplicity is always an ordinary integer, this holds for every
function, differentially algebraic or hypertranscendental: the concrete refutation of the conjectured
dichotomy, since eventual periodicity is universal and so cannot single out the differentially
algebraic class. -/
theorem deckCharge_determined_by_order {f g : ℂ → ℂ} {ρ σ : ℂ}
    (h : (analyticOrderAt f ρ).toNat = (analyticOrderAt g σ).toNat) (k : ℕ) :
    deckCharge f k ρ = deckCharge g k σ := by
  unfold deckCharge; rw [h]

/-- **Beyond the `2`-adic height the charge is never trivial.**  For a point of positive finite order,
the level-`k` charge is not `1` once `k` exceeds the `2`-adic valuation of the multiplicity.  With
`deckCharge_eq_one_iff_le_val` this pins the triviality pattern to the threshold `{k : k ≤ v₂(ord)}`:
the sequence `k ↦ (deckCharge f k ρ = 1)` is `true` up to the valuation and `false` thereafter — an
eventually-constant, hence eventually-periodic, Boolean sequence, at every function. -/
theorem deckCharge_ne_one_of_gt_val (f : ℂ → ℂ) {ρ : ℂ}
    (hord : (analyticOrderAt f ρ).toNat ≠ 0) {k : ℕ}
    (hk : (analyticOrderAt f ρ).toNat.factorization 2 < k) :
    deckCharge f k ρ ≠ 1 := by
  rw [ne_eq, deckCharge_eq_one_iff_le_val f k hord]; omega

/-! ### §5 Translation covariance and the difference-recurrence

The charge transports under the additive shift `z ↦ z + c`, and along a difference equation
`f(s+1) = M(s)·f(s)` with `M` a nonvanishing analytic unit at the shift points, the order — and hence
the charge — is *constant* along the orbit `{ρ + n}`.  So even a hypertranscendental function carrying
a functional equation (`Γ`, `1/Γ`) has an eventually-periodic charge sequence along its shift orbit: a
second, independent witness that eventual periodicity cannot detect differential algebraicity. -/

/-- Analyticity is invariant under the additive shift `z ↦ z + c`. -/
theorem analyticAt_comp_add_iff (f : ℂ → ℂ) (c ρ : ℂ) :
    AnalyticAt ℂ (fun z => f (z + c)) ρ ↔ AnalyticAt ℂ f (ρ + c) := by
  constructor
  · intro h
    have hshift : AnalyticAt ℂ (fun z : ℂ => z - c) (ρ + c) := by fun_prop
    have hcomp := AnalyticAt.comp_of_eq h hshift (by ring)
    have he : (fun z => f (z + c)) ∘ (fun z : ℂ => z - c) = f := by funext z; simp
    rwa [he] at hcomp
  · intro h
    have hshift : AnalyticAt ℂ (fun z : ℂ => z + c) ρ := by fun_prop
    have hcomp := AnalyticAt.comp_of_eq h hshift (by ring)
    simpa [Function.comp] using hcomp

/-- Eventual statements transport across the shift homeomorphism `z ↦ z + c`. -/
theorem eventually_comp_add_iff (c ρ : ℂ) (P : ℂ → Prop) :
    (∀ᶠ z in nhds ρ, P (z + c)) ↔ (∀ᶠ w in nhds (ρ + c), P w) := by
  have h1 : Filter.Tendsto (fun z : ℂ => z + c) (nhds ρ) (nhds (ρ + c)) := by
    simpa using (Continuous.tendsto (by fun_prop) ρ)
  have h2 : Filter.Tendsto (fun w : ℂ => w - c) (nhds (ρ + c)) (nhds ρ) := by
    simpa using (Continuous.tendsto (show Continuous (fun w : ℂ => w - c) by fun_prop) (ρ + c))
  exact ⟨fun h => by filter_upwards [h2.eventually h] with w hw; simpa using hw,
        fun h => h1.eventually h⟩

/-- Infinite vanishing order (identical local vanishing) transports under the shift. -/
theorem analyticOrderAt_eq_top_comp_add_iff (f : ℂ → ℂ) (c ρ : ℂ) :
    analyticOrderAt (fun z => f (z + c)) ρ = ⊤ ↔ analyticOrderAt f (ρ + c) = ⊤ := by
  rw [analyticOrderAt_eq_top, analyticOrderAt_eq_top]
  exact eventually_comp_add_iff c ρ (fun w => f w = 0)

/-- **Translation invariance of the vanishing order.**  `ord_ρ(f(·+c)) = ord_{ρ+c}(f)`: the additive
shift is an order-preserving automorphism of the local divisor.  Proved by transporting the
Weierstrass factorization `f = (·-(ρ+c))^n • g` (with `g` analytic, nonvanishing) along the shift; the
non-analytic and infinite-order cases transport directly. -/
theorem analyticOrderAt_comp_add (f : ℂ → ℂ) (c ρ : ℂ) :
    analyticOrderAt (fun z => f (z + c)) ρ = analyticOrderAt f (ρ + c) := by
  by_cases hana : AnalyticAt ℂ f (ρ + c)
  · have hg : AnalyticAt ℂ (fun z => f (z + c)) ρ := (analyticAt_comp_add_iff f c ρ).mpr hana
    by_cases htop : analyticOrderAt f (ρ + c) = ⊤
    · rw [htop, (analyticOrderAt_eq_top_comp_add_iff f c ρ).mpr htop]
    · have hgtop : analyticOrderAt (fun z => f (z + c)) ρ ≠ ⊤ :=
        fun h => htop ((analyticOrderAt_eq_top_comp_add_iff f c ρ).mp h)
      set n := (analyticOrderAt f (ρ + c)).toNat with hn
      obtain ⟨h, hh_an, hh_ne, hh_eq⟩ :=
        (hana.analyticOrderNatAt_eq_iff htop (n := n)).mp (by rw [analyticOrderNatAt])
      have hgfac : ∀ᶠ z in nhds ρ,
          (fun z => f (z + c)) z = (z - ρ) ^ n • (fun z => h (z + c)) z := by
        have hev :=
          (eventually_comp_add_iff c ρ (fun w => f w = (w - (ρ + c)) ^ n • h w)).mpr hh_eq
        filter_upwards [hev] with z hz
        show f (z + c) = (z - ρ) ^ n • h (z + c)
        rw [show (z - ρ) = (z + c - (ρ + c)) by ring]
        exact hz
      have hgan : AnalyticAt ℂ (fun z => h (z + c)) ρ := (analyticAt_comp_add_iff h c ρ).mpr hh_an
      have hgne : (fun z => h (z + c)) ρ ≠ 0 := hh_ne
      have hnat : analyticOrderNatAt (fun z => f (z + c)) ρ = n :=
        (hg.analyticOrderNatAt_eq_iff hgtop).mpr ⟨_, hgan, hgne, hgfac⟩
      rw [← ENat.coe_toNat hgtop, ← ENat.coe_toNat htop, ← hn]
      rw [analyticOrderNatAt] at hnat
      exact_mod_cast hnat
  · rw [analyticOrderAt_eq_zero.mpr (Or.inl hana),
      analyticOrderAt_eq_zero.mpr (Or.inl (fun hc => hana ((analyticAt_comp_add_iff f c ρ).mp hc)))]

/-- **Translation covariance of the charge.**  `deckCharge (f(·+c)) k ρ = deckCharge f k (ρ+c)`: the
charge follows the divisor under the additive shift. -/
theorem deckCharge_comp_add (f : ℂ → ℂ) (k : ℕ) (c ρ : ℂ) :
    deckCharge (fun z => f (z + c)) k ρ = deckCharge f k (ρ + c) := by
  unfold deckCharge; rw [analyticOrderAt_comp_add]

/-- **Difference-recurrence for the order.**  If `f(s+1) = M(s)·f(s)` with `M` analytic and
nonvanishing at every orbit point `ρ + n`, the vanishing order is *constant* along the shift orbit:
`ord_{ρ+n}(f) = ord_ρ(f)`.  The unit multiplier contributes zero order at each step, so the
translation recurrence `ord_{ρ+n+1}(f) = ord_ρ(M) + ord_{ρ+n}(f)` collapses. -/
theorem analyticOrderAt_orbit_const {f M : ℂ → ℂ} (ρ : ℂ)
    (hFE : (fun z => f (z + 1)) = M * f)
    (hMan : ∀ n : ℕ, AnalyticAt ℂ M (ρ + n)) (hMne : ∀ n : ℕ, M (ρ + n) ≠ 0)
    (hfan : ∀ n : ℕ, AnalyticAt ℂ f (ρ + n)) :
    ∀ n : ℕ, analyticOrderAt f (ρ + n) = analyticOrderAt f ρ := by
  have step : ∀ n : ℕ,
      analyticOrderAt f (ρ + ((n : ℂ) + 1)) = analyticOrderAt f (ρ + (n : ℂ)) := by
    intro n
    have ht := analyticOrderAt_comp_add f 1 (ρ + (n : ℂ))
    rw [hFE, analyticOrderAt_mul (hMan n) (hfan n),
      analyticOrderAt_eq_zero.mpr (Or.inr (hMne n)), zero_add] at ht
    rw [show ρ + ((n : ℂ) + 1) = (ρ + (n : ℂ)) + 1 by ring]
    exact ht.symm
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
    have hc : (↑(m + 1) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
    rw [hc, step m, ih]

/-- **Difference-recurrence for the charge.**  Under the same functional equation with a nonvanishing
analytic unit multiplier along the orbit, the charge is *constant* along the shift orbit:
`deckCharge f k (ρ+n) = deckCharge f k ρ`.  Hypertranscendental solutions of a difference equation
(`Γ`, `1/Γ`) therefore have an eventually-periodic charge sequence along their orbit — an independent
confirmation that eventual periodicity is blind to the differential-algebraic class. -/
theorem deckCharge_orbit_const {f M : ℂ → ℂ} (ρ : ℂ) (k : ℕ)
    (hFE : (fun z => f (z + 1)) = M * f)
    (hMan : ∀ n : ℕ, AnalyticAt ℂ M (ρ + n)) (hMne : ∀ n : ℕ, M (ρ + n) ≠ 0)
    (hfan : ∀ n : ℕ, AnalyticAt ℂ f (ρ + n)) :
    ∀ n : ℕ, deckCharge f k (ρ + n) = deckCharge f k ρ := by
  intro n
  unfold deckCharge
  rw [analyticOrderAt_orbit_const ρ hFE hMan hMne hfan n]

end RHTower
