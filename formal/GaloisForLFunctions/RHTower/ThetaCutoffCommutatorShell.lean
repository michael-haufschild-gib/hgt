import GaloisForLFunctions.RHTower.ThetaIntegerCutoffMovingPacket

/-!
# The theta cutoff commutator: exact shell, sieve discrepancy, and moving limit

Let `K_N = Σ_{n ≤ N} a_n` be the integer cutoff of the completed theta source and `D_S` the literal
deletion of a finite prime set `S`, `P = ∏_{p ∈ S} p`.  Applying the deletion before cutting differs
from cutting the deleted source by exactly the atoms crossing `N`:

`C_{S,N} = D_S K_N − Σ_{m ≤ N, (m,P) = 1} a_m = Σ_{d | P} μ(d) Σ_{N < dn ≤ dN} a_{dn}`,

written over the subsets `T ⊆ S` with `d = ∏ T`.  In the moving frame `x = y − log N` the critical
density of each shell is a Riemann sum with mesh `d/N` of the profile `q_y(t) = e^y h(e^y t)`.
First-order Euler summation against the sawtooth gives the exact shell error

`(1/d)[h Σ q_y(nh) − ∫_1^d q_y] = (1/N)[{N/d} q_y(1) + ∫_1^d {Nt/d} q_y'(t) dt]`,

and summing over `d | P` gives the source-weighted sieve discrepancy identity

`e^{(y−log N)/2} C_{S,N}(y − log N) − C_S(y) = q_y(1) A_S(N)/N + (1/N) ∫_1^P q_y'(t) H_{S,N}(t) dt`,

with `A_S(X) = Σ μ(d){X/d} = X E_S(1) − R_S(X)`.  The limit profile is
`C_S(y) = −2π e^{3y}[Σ_{d|P} μ(d) d² e^{−πd² e^{2y}} − E_S(1) e^{−π e^{2y}}]`, and for fixed `S` the
moving density converges to it uniformly on the whole line.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## The exact cutoff commutator shell -/

/-- The rough cutoff `Σ_{m ≤ N, (m, P) = 1} a_m`. -/
def roughCutoffThetaSource (S : Finset ℕ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ m ∈ (Finset.Icc 1 N).filter (fun m => ∀ p ∈ S, ¬ p ∣ m), thetaCuspSourceTerm x m

/-- The cutoff commutator source `C_{S,N} = D_S K_N − Σ_{m ≤ N, (m,P) = 1} a_m`. -/
def cutoffCommutatorSource (S : Finset ℕ) (N : ℕ) (x : ℝ) : ℝ :=
  thetaPrimeDeletion S (integerCutoffThetaSource N) x - roughCutoffThetaSource S N x

theorem thetaPrimeDeletion_integerCutoffThetaSource (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (N : ℕ) (x : ℝ) :
    thetaPrimeDeletion S (integerCutoffThetaSource N) x =
      ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card *
        ∑ n ∈ Finset.Icc 1 N, thetaCuspSourceTerm x ((∏ p ∈ T, p) * n) := by
  unfold thetaPrimeDeletion integerCutoffThetaSource
  refine Finset.sum_congr rfl fun T hT => ?_
  have hpos : 0 < ∏ p ∈ T, p :=
    Finset.prod_pos fun p hp => (hS p (Finset.mem_powerset.mp hT hp)).pos
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  exact rpow_neg_half_mul_thetaCuspSourceTerm_add_log hpos x n

/-- Multiples of `d` up to `N` are `d n`, `n ≤ N / d`. -/
theorem sum_Icc_filter_dvd_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) {d : ℕ} (hd : 0 < d)
    (N : ℕ) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => d ∣ m), f m = ∑ n ∈ Finset.Icc 1 (N / d), f (d * n) := by
  refine (Finset.sum_nbij' (fun n => d * n) (fun m => m / d) ?_ ?_ ?_ ?_ ?_).symm
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    have h2 := (Nat.le_div_iff_mul_le hd).1 hn.2
    refine ⟨⟨by nlinarith, by linarith [mul_comm n d]⟩, dvd_mul_right d n⟩
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hm
    rw [Nat.mul_div_cancel_left k hd]
    refine ⟨Nat.pos_of_ne_zero fun h => by simp [h] at h1, ?_⟩
    exact (Nat.le_div_iff_mul_le hd).2 (by linarith [mul_comm k d])
  · intro n _
    exact Nat.mul_div_cancel_left n hd
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    exact Nat.mul_div_cancel' hm.2
  · intro n _
    rfl

/-- **Legendre inclusion–exclusion** over the subsets of a finite set of primes. -/
theorem sum_filter_coprime_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) (f : ℕ → ℝ) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => ∀ p ∈ S, ¬ p ∣ m), f m =
      ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card *
        ∑ n ∈ Finset.Icc 1 (N / ∏ p ∈ T, p), f ((∏ p ∈ T, p) * n) := by
  classical
  have hind : ∀ m : ℕ, (if ∀ p ∈ S, ¬ p ∣ m then (1 : ℝ) else 0) =
      ∑ T ∈ S.powerset, if (∏ p ∈ T, p) ∣ m then (-1 : ℝ) ^ T.card else 0 := fun m => by
    have hiff : ∀ T ∈ S.powerset, ((∏ p ∈ T, p) ∣ m ↔ T ⊆ S.filter (· ∣ m)) := fun T hT => by
      have hTS := Finset.mem_powerset.mp hT
      constructor
      · intro h q hq
        exact Finset.mem_filter.mpr ⟨hTS hq, (Finset.dvd_prod_of_mem (fun p => p) hq).trans h⟩
      · intro h
        exact Finset.prod_primes_dvd m (fun q hq => (hS q (hTS hq)).prime)
          (fun q hq => (Finset.mem_filter.mp (h hq)).2)
    rw [Finset.sum_congr rfl fun T hT => by rw [if_congr (hiff T hT) rfl rfl]]
    rw [← Finset.sum_filter, show S.powerset.filter (fun T => T ⊆ S.filter (· ∣ m)) =
      (S.filter (· ∣ m)).powerset by
        ext T; simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨fun h => h.2, fun h => ⟨h.trans (Finset.filter_subset _ _), h⟩⟩,
      show (∑ a ∈ (S.filter (· ∣ m)).powerset, (-1 : ℝ) ^ a.card) =
        ((∑ a ∈ (S.filter (· ∣ m)).powerset, (-1 : ℤ) ^ a.card : ℤ) : ℝ) by push_cast; rfl,
      Finset.sum_powerset_neg_one_pow_card]
    simp only [Finset.filter_eq_empty_iff]
    split_ifs <;> simp
  rw [Finset.sum_filter]
  simp_rw [show ∀ m, (if ∀ p ∈ S, ¬ p ∣ m then f m else 0) =
      (if ∀ p ∈ S, ¬ p ∣ m then (1 : ℝ) else 0) * f m from fun m => by
    split_ifs <;> simp, hind, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hpos : 0 < ∏ p ∈ T, p :=
    Finset.prod_pos fun p hp => (hS p (Finset.mem_powerset.mp hT hp)).pos
  rw [← sum_Icc_filter_dvd_eq _ hpos, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> simp

theorem roughCutoffThetaSource_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) (x : ℝ) :
    roughCutoffThetaSource S N x =
      ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card *
        ∑ n ∈ Finset.Icc 1 (N / ∏ p ∈ T, p), thetaCuspSourceTerm x ((∏ p ∈ T, p) * n) :=
  sum_filter_coprime_eq S hS N (thetaCuspSourceTerm x)

/-- **(1) The exact cutoff commutator shell.**
`C_{S,N} = Σ_{d|P} μ(d) Σ_{N < dn ≤ dN} a_{dn}`, written over the subsets `T ⊆ S`, `d = ∏T`. -/
theorem cutoffCommutatorSource_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) (x : ℝ) :
    cutoffCommutatorSource S N x =
      ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card *
        ∑ n ∈ Finset.Ioc (N / ∏ p ∈ T, p) N, thetaCuspSourceTerm x ((∏ p ∈ T, p) * n) := by
  rw [cutoffCommutatorSource, thetaPrimeDeletion_integerCutoffThetaSource S hS,
    roughCutoffThetaSource_eq S hS, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← mul_sub]
  congr 1
  have hle : N / (∏ p ∈ T, p) ≤ N := Nat.div_le_self N _
  generalize N / (∏ p ∈ T, p) = q at hle ⊢
  rw [sub_eq_iff_eq_add', ← Finset.sum_union]
  · congr 1
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  · rw [Finset.disjoint_left]
    intro n h1 h2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2
    omega

/-- The `d = 1` shell is empty; for one prime the commutator is `−Σ_{N/p < n ≤ N} a_{pn}`. -/
theorem cutoffCommutatorSource_singleton {p : ℕ} (hp : p.Prime) (N : ℕ) (x : ℝ) :
    cutoffCommutatorSource {p} N x =
      -∑ n ∈ Finset.Ioc (N / p) N, thetaCuspSourceTerm x (p * n) := by
  rw [cutoffCommutatorSource_eq {p} (by simpa using hp), show ({p} : Finset ℕ) = insert p ∅ from rfl,
    Finset.sum_powerset_insert (Finset.notMem_empty p)]
  simp

/-! ## First-order Euler summation against the sawtooth -/

theorem intervalIntegrable_fract_mul_continuous {g : ℝ → ℝ} (hg : Continuous g) (a b : ℝ) :
    IntervalIntegrable (fun u => Int.fract u * g u) volume a b := by
  rw [intervalIntegrable_iff]
  exact ((hg.intervalIntegrable a b).def'.bdd_mul
    ((by measurability : Measurable (Int.fract : ℝ → ℝ)).aestronglyMeasurable) (c := 1)
    (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg u)]
      exact (Int.fract_lt_one u).le))

/-- One sawtooth cell: for `k ≤ a ≤ c ≤ k + 1`,
`∫_a^c {u} f'(u) du = (c − k) f(c) − (a − k) f(a) − ∫_a^c f`. -/
theorem integral_fract_mul_deriv_cell {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') {k : ℕ} {a c : ℝ} (hka : (k : ℝ) ≤ a) (hac : a ≤ c)
    (hck : c ≤ k + 1) :
    ∫ u in a..c, Int.fract u * f' u = (c - k) * f c - (a - k) * f a - ∫ u in a..c, f u := by
  have hcongr : ∫ u in a..c, Int.fract u * f' u = ∫ u in a..c, (u - k) * f' u := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume ((k : ℝ) + 1)] with u hu hmem
    rw [uIoc_of_le hac] at hmem
    congr 1
    rw [Int.fract_eq_iff]
    refine ⟨by linarith [hmem.1], lt_of_le_of_ne (by linarith [hmem.2]) (fun h => hu (by linarith)),
      k, by push_cast; ring⟩
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := c)
    (u := fun u => u - (k : ℝ)) (u' := fun _ => (1 : ℝ)) (v := f) (v' := f')
    (fun x _ => (hasDerivAt_id x).sub_const _) (fun x _ => hf x) intervalIntegrable_const
    (hf'.intervalIntegrable _ _)
  rw [hcongr, hibp]
  simp only [one_mul]

/-- **First-order Euler summation.**  For `0 ≤ a ≤ b` with `b` an integer,
`Σ_{a < n ≤ b} f(n) = ∫_a^b f + ∫_a^b {u} f'(u) du + {a} f(a)`. -/
theorem sum_Ioc_floor_eq_integral {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') {a : ℝ} (ha : 0 ≤ a) {b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ b, f n =
      (∫ u in a..(b : ℝ), f u) + (∫ u in a..(b : ℝ), Int.fract u * f' u) + Int.fract a * f a := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  set k := ⌊a⌋₊ with hk
  have hfa : Int.fract a = a - k := by
    rw [Int.fract, ← natCast_floor_eq_intCast_floor ha]
  have hka : (k : ℝ) ≤ a := Nat.floor_le ha
  have hak : a < k + 1 := Nat.lt_floor_add_one a
  rcases Nat.lt_or_ge k b with hkb | hkb
  · induction b, hkb using Nat.le_induction with
    | base =>
      rw [Nat.Ioc_succ_singleton, Finset.sum_singleton, hfa,
        show ((k.succ : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring,
        integral_fract_mul_deriv_cell hf hf' hka hak.le le_rfl]
      ring
    | succ b hb ih =>
      have hbk : k ≤ b := by omega
      have hab' : a ≤ b := by
        have : ((k + 1 : ℕ) : ℝ) ≤ b := by exact_mod_cast hb
        push_cast at this; linarith
      rw [Finset.sum_Ioc_succ_top hbk, ih hab',
        ← intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable a b)
          (hfc.intervalIntegrable b (b + 1 : ℕ)),
        ← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_fract_mul_continuous hf' a b)
          (intervalIntegrable_fract_mul_continuous hf' b (b + 1 : ℕ)),
        integral_fract_mul_deriv_cell hf hf' (k := b) le_rfl (by push_cast; linarith)
          (by push_cast; linarith)]
      push_cast
      ring
  · have hkb' : b = k := le_antisymm hkb ((Nat.floor_mono hab).trans_eq (Nat.floor_natCast b))
    have hab2 : a = b := by
      have : (b : ℝ) ≤ a := by rw [hkb']; exact hka
      linarith
    subst hab2
    rw [hkb', Finset.Ioc_self, Finset.sum_empty, intervalIntegral.integral_same,
      intervalIntegral.integral_same, Int.fract_natCast]
    ring

/-- **(3a) Exact shell quadrature error.**  With mesh `h = d/N`,
`(1/d)[h Σ_{1 < nh ≤ d} q(nh) − ∫_1^d q] = (1/N)[{N/d} q(1) + ∫_1^d {Nt/d} q'(t) dt]`. -/
theorem shell_quadrature_error {q q' : ℝ → ℝ} (hq : ∀ t, HasDerivAt q (q' t) t)
    (hq' : Continuous q') {d N : ℕ} (hd : 0 < d) (hN : 0 < N) :
    (1 / d : ℝ) * ((d / N : ℝ) * ∑ n ∈ Finset.Ioc (N / d) N, q ((d / N : ℝ) * n) -
        ∫ t in (1 : ℝ)..d, q t) =
      (1 / N : ℝ) * (Int.fract ((N : ℝ) / d) * q 1 + ∫ t in (1 : ℝ)..d, Int.fract (N * t / d) * q' t) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set h : ℝ := (d : ℝ) / N with hh
  have hh0 : 0 < h := div_pos hdR hNR
  have hf : ∀ u, HasDerivAt (fun u => q (h * u)) (h * q' (h * u)) u := fun u => by
    have := (hq (h * u)).comp u ((hasDerivAt_id u).const_mul h)
    simp only [mul_one] at this
    exact this.congr_deriv (mul_comm _ _)
  have hfc' : Continuous fun u => h * q' (h * u) := by
    exact continuous_const.mul (hq'.comp (continuous_const.mul continuous_id))
  have hle : (N : ℝ) / d ≤ N := div_le_self hNR.le (by exact_mod_cast hd)
  have hE := sum_Ioc_floor_eq_integral hf hfc' (div_nonneg hNR.le hdR.le) hle
  rw [Nat.floor_div_eq_div] at hE
  have ha1 : h * ((N : ℝ) / d) = 1 := by rw [hh]; field_simp
  have hN1 : h * (N : ℝ) = d := by rw [hh]; field_simp
  have hI1 : (∫ u in ((N : ℝ) / d)..(N : ℝ), q (h * u)) = h⁻¹ * ∫ t in (1 : ℝ)..d, q t := by
    rw [intervalIntegral.integral_comp_mul_left (fun t => q t) hh0.ne', ha1, hN1, smul_eq_mul]
  have hI2 : (∫ u in ((N : ℝ) / d)..(N : ℝ), Int.fract u * (h * q' (h * u))) =
      ∫ t in (1 : ℝ)..d, Int.fract (N * t / d) * q' t := by
    have hG : ∀ u : ℝ, Int.fract u * (h * q' (h * u)) =
        (fun t => Int.fract (t / h) * h * q' t) (h * u) := fun u => by
      simp only
      rw [mul_div_cancel_left₀ u hh0.ne']
      ring
    simp_rw [hG]
    rw [intervalIntegral.integral_comp_mul_left (fun t => Int.fract (t / h) * h * q' t) hh0.ne', ha1,
      hN1, smul_eq_mul, ← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    rw [hh, show t / ((d : ℝ) / N) = N * t / d by field_simp]
    field_simp
  rw [ha1] at hE
  rw [hE, hI1, hI2]
  generalize (∫ t in (1 : ℝ)..d, q t) = I
  generalize (∫ t in (1 : ℝ)..d, Int.fract (N * t / d) * q' t) = J
  rw [hh]
  field_simp
  ring

/-! ## The moving shell and its boundary profile -/

/-- The moving seed profile `q_y(t) = e^y h(e^y t)`. -/
def movingSeedProfile (y t : ℝ) : ℝ := Real.exp y * thetaCuspSeed (Real.exp y * t)

/-- The derivative `h'(t) = 2π(−4π² t⁵ + 14π t³ − 6t) e^{−πt²}` of the theta-cusp seed. -/
def thetaCuspSeedDeriv (t : ℝ) : ℝ :=
  2 * Real.pi * (-(4 * Real.pi ^ 2) * t ^ 5 + 14 * Real.pi * t ^ 3 - 6 * t) *
    Real.exp (-Real.pi * t ^ 2)

theorem hasDerivAt_thetaCuspSeed (t : ℝ) : HasDerivAt thetaCuspSeed (thetaCuspSeedDeriv t) t := by
  have h := (((((hasDerivAt_pow 4 t).const_mul (2 * Real.pi)).sub
    ((hasDerivAt_pow 2 t).const_mul 3)).mul
      (((hasDerivAt_pow 2 t).const_mul (-Real.pi)).exp)).const_mul (2 * Real.pi))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  · simp only [thetaCuspSeedDeriv, Nat.cast_ofNat, Pi.sub_apply]
    ring
  · simp only [thetaCuspSeed, Pi.sub_apply, Pi.mul_apply]
    ring

theorem continuous_thetaCuspSeedDeriv : Continuous thetaCuspSeedDeriv := by
  unfold thetaCuspSeedDeriv; fun_prop

theorem hasDerivAt_seedProfile (y t : ℝ) :
    HasDerivAt (movingSeedProfile y) (Real.exp y ^ 2 * thetaCuspSeedDeriv (Real.exp y * t)) t := by
  have h := ((hasDerivAt_thetaCuspSeed (Real.exp y * t)).comp t
    ((hasDerivAt_id t).const_mul (Real.exp y))).const_mul (Real.exp y)
  refine h.congr_deriv ?_
  simp only [mul_one]
  ring

/-- The moving shell density `e^{(y − log N)/2} C_{S,N}(y − log N)`. -/
def movingCommutatorDensity (S : Finset ℕ) (N : ℕ) (y : ℝ) : ℝ :=
  Real.exp ((1 / 2 : ℝ) * (y - Real.log N)) * cutoffCommutatorSource S N (y - Real.log N)

/-- The boundary profile `C_S(y) = Σ_{d|P} μ(d)/d ∫_1^d q_y`. -/
def commutatorBoundaryProfile (S : Finset ℕ) (y : ℝ) : ℝ :=
  ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card *
    ((1 / (∏ p ∈ T, p : ℕ) : ℝ) * ∫ t in (1 : ℝ)..(∏ p ∈ T, p : ℕ), movingSeedProfile y t)

theorem exp_half_mul_thetaCuspSourceTerm_moving {N : ℕ} (hN : 0 < N) (y : ℝ) (m : ℕ) :
    Real.exp ((1 / 2 : ℝ) * (y - Real.log N)) * thetaCuspSourceTerm (y - Real.log N) m =
      (1 / N : ℝ) * movingSeedProfile y (m / N) := by
  have hsq : Real.exp ((1 / 2 : ℝ) * (y - Real.log N)) * Real.exp ((y - Real.log N) / 2) =
      Real.exp y / N := by
    rw [← Real.exp_add, show (1 / 2 : ℝ) * (y - Real.log N) + (y - Real.log N) / 2 =
      y - Real.log N by ring, exp_sub_log_natCast hN]
  rw [thetaCuspSourceTerm, ← mul_assoc, hsq, exp_sub_log_natCast hN, movingSeedProfile]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- The moving shell is a signed sum of Riemann sums with meshes `d/N`. -/
theorem movingCommutatorDensity_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {N : ℕ} (hN : 0 < N)
    (y : ℝ) :
    movingCommutatorDensity S N y =
      ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * ((1 / (∏ p ∈ T, p : ℕ) : ℝ) *
        (((∏ p ∈ T, p : ℕ) / N : ℝ) * ∑ n ∈ Finset.Ioc (N / ∏ p ∈ T, p) N,
          movingSeedProfile y (((∏ p ∈ T, p : ℕ) / N : ℝ) * n))) := by
  rw [movingCommutatorDensity, cutoffCommutatorSource_eq S hS, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hd : 0 < ∏ p ∈ T, p := Finset.prod_pos fun p hp => (hS p (Finset.mem_powerset.mp hT hp)).pos
  have hdR : ((∏ p ∈ T, p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [← mul_assoc, mul_comm (Real.exp _) ((-1 : ℝ) ^ T.card), mul_assoc]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [exp_half_mul_thetaCuspSourceTerm_moving hN, Nat.cast_mul,
    show ((∏ p ∈ T, p : ℕ) : ℝ) * n / N = ((∏ p ∈ T, p : ℕ) / N : ℝ) * n by ring]
  field_simp

/-- The Euler factor `E_S(1) = ∏_{p∈S} (1 − 1/p) = Σ_{d|P} μ(d)/d`. -/
theorem prod_one_sub_inv_eq_sum_powerset (S : Finset ℕ) :
    ∏ p ∈ S, (1 - (p : ℝ)⁻¹) = ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * (1 / (∏ p ∈ T, p : ℕ)) := by
  classical
  have h := Finset.prod_add (fun p : ℕ => -(p : ℝ)⁻¹) (fun _ => (1 : ℝ)) S
  simp only [Finset.prod_const_one, mul_one] at h
  rw [show ∏ p ∈ S, (1 - (p : ℝ)⁻¹) = ∏ p ∈ S, (-(p : ℝ)⁻¹ + 1) from
    Finset.prod_congr rfl fun p _ => by ring, h]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_neg, Finset.prod_inv_distrib]
  push_cast
  ring

/-- **(2) Closed boundary profile.**
`C_S(y) = −2π e^{3y}[Σ_{d|P} μ(d) d² e^{−πd² e^{2y}} − E_S(1) e^{−π e^{2y}}]`. -/
theorem commutatorBoundaryProfile_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (y : ℝ) :
    commutatorBoundaryProfile S y =
      -(2 * Real.pi) * Real.exp (3 * y) *
        ((∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * ((∏ p ∈ T, p : ℕ) : ℝ) ^ 2 *
            Real.exp (-(Real.pi * ((∏ p ∈ T, p : ℕ) : ℝ) ^ 2 * Real.exp (2 * y)))) -
          (∏ p ∈ S, (1 - (p : ℝ)⁻¹)) * Real.exp (-(Real.pi * Real.exp (2 * y)))) := by
  have hint : ∀ c : ℝ, 0 < c → (∫ t in (1 : ℝ)..c, movingSeedProfile y t) =
      -(2 * Real.pi) * Real.exp (3 * y) * (c ^ 3 * Real.exp (-(Real.pi * c ^ 2 * Real.exp (2 * y))) -
        Real.exp (-(Real.pi * Real.exp (2 * y)))) := fun c _ => by
    have hF : ∀ t, HasDerivAt (fun t => -(2 * Real.pi) * ((Real.exp y * t) ^ 3 *
        Real.exp (-Real.pi * (Real.exp y * t) ^ 2))) (movingSeedProfile y t) t := fun t => by
      have := (hasDerivAt_thetaCuspSeed_primitive (Real.exp y * t)).comp t
        ((hasDerivAt_id t).const_mul (Real.exp y))
      refine this.congr_deriv ?_
      simp only [movingSeedProfile, mul_one]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t)
      ((continuous_const.mul (continuous_thetaCuspSeed.comp
        (continuous_const.mul continuous_id))).intervalIntegrable _ _)]
    have e3 : Real.exp y ^ 3 = Real.exp (3 * y) := by rw [← Real.exp_nat_mul]; norm_num
    have e2 : Real.exp y ^ 2 = Real.exp (2 * y) := by rw [← Real.exp_nat_mul]; norm_num
    simp only [mul_pow, mul_one, e3, e2]
    rw [show -Real.pi * (Real.exp (2 * y) * c ^ 2) = -(Real.pi * c ^ 2 * Real.exp (2 * y)) by ring,
      show -Real.pi * Real.exp (2 * y) = -(Real.pi * Real.exp (2 * y)) by ring]
    ring
  rw [commutatorBoundaryProfile, prod_one_sub_inv_eq_sum_powerset, Finset.sum_mul,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hd : 0 < ∏ p ∈ T, p := Finset.prod_pos fun p hp => (hS p (Finset.mem_powerset.mp hT hp)).pos
  have hdR : (0 : ℝ) < ((∏ p ∈ T, p : ℕ) : ℝ) := by exact_mod_cast hd
  rw [hint _ hdR]
  field_simp

/-! ## The signed sieve discrepancy -/

/-- The rough count `R_S(X) = #{1 ≤ m ≤ X : (m, P) = 1}`. -/
def roughCount (S : Finset ℕ) (X : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊X⌋₊).filter (fun m => ∀ p ∈ S, ¬ p ∣ m)).card

/-- The centered rough-number discrepancy `A_S(X) = Σ_{d|P} μ(d) {X/d}`. -/
def roughDiscrepancy (S : Finset ℕ) (X : ℝ) : ℝ :=
  ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * Int.fract (X / (∏ p ∈ T, p : ℕ))

/-- The tail discrepancy `H_{S,N}(t) = Σ_{d|P, d ≥ t} μ(d) {Nt/d}`. -/
def roughTailDiscrepancy (S : Finset ℕ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ T ∈ S.powerset, (Iic ((∏ p ∈ T, p : ℕ) : ℝ)).indicator
    (fun t => (-1 : ℝ) ^ T.card * Int.fract (N * t / (∏ p ∈ T, p : ℕ))) t

/-- **(3b)** `A_S(X) = X E_S(1) − R_S(X)` for `X ≥ 0`. -/
theorem roughDiscrepancy_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {X : ℝ} (hX : 0 ≤ X) :
    roughDiscrepancy S X = X * ∏ p ∈ S, (1 - (p : ℝ)⁻¹) - roughCount S X := by
  have hcount : (roughCount S X : ℝ) =
      ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * ((⌊X⌋₊ / ∏ p ∈ T, p : ℕ) : ℝ) := by
    rw [roughCount, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
      sum_filter_coprime_eq S hS ⌊X⌋₊ (fun _ => 1)]
    simp
  rw [hcount, prod_one_sub_inv_eq_sum_powerset, Finset.mul_sum, ← Finset.sum_sub_distrib,
    roughDiscrepancy]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hd : 0 < ∏ p ∈ T, p := Finset.prod_pos fun p hp => (hS p (Finset.mem_powerset.mp hT hp)).pos
  have hdR : (0 : ℝ) < ((∏ p ∈ T, p : ℕ) : ℝ) := by exact_mod_cast hd
  have hfl : ((⌊X⌋₊ / ∏ p ∈ T, p : ℕ) : ℝ) = ⌊X / (∏ p ∈ T, p : ℕ)⌋₊ := by
    rw [Nat.floor_div_natCast]
  rw [hfl, Int.fract, ← natCast_floor_eq_intCast_floor (div_nonneg hX hdR.le)]
  ring

theorem measurable_fract_mul_div (N d : ℝ) : Measurable fun t : ℝ => Int.fract (N * t / d) :=
  measurable_fract.comp (by fun_prop)

theorem intervalIntegrable_indicator_fract_mul {g : ℝ → ℝ} (hg : Continuous g) (N d e c : ℝ)
    (a b : ℝ) :
    IntervalIntegrable (fun t => (Iic c).indicator (fun t => e * Int.fract (N * t / d)) t * g t)
      volume a b := by
  rw [intervalIntegrable_iff]
  have hm : Measurable fun t => (Iic c).indicator (fun t => e * Int.fract (N * t / d)) t :=
    (measurable_const.mul (measurable_fract_mul_div N d)).indicator measurableSet_Iic
  exact ((hg.intervalIntegrable a b).def'.bdd_mul hm.aestronglyMeasurable (c := |e|)
    (ae_of_all _ fun t => by
      by_cases ht : t ∈ Iic c
      · rw [Set.indicator_of_mem ht, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (Int.fract_nonneg (N * t / d))]
        exact mul_le_of_le_one_right (abs_nonneg e) (Int.fract_lt_one _).le
      · rw [Set.indicator_of_notMem ht, norm_zero]; exact abs_nonneg e))

theorem intervalIntegrable_fract_mul_div {g : ℝ → ℝ} (hg : Continuous g) (N d a b : ℝ) :
    IntervalIntegrable (fun t => Int.fract (N * t / d) * g t) volume a b := by
  rw [intervalIntegrable_iff]
  exact ((hg.intervalIntegrable a b).def'.bdd_mul (measurable_fract_mul_div N d).aestronglyMeasurable
    (c := 1) (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
      exact (Int.fract_lt_one _).le))

/-- Truncating an interval integral at `d` is integrating the `Iic d` indicator. -/
theorem intervalIntegral_eq_indicator_Iic {F : ℝ → ℝ} {a d P : ℝ} (had : a ≤ d) (hdP : d ≤ P)
    (hF : IntervalIntegrable F volume a P) :
    ∫ t in a..d, F t = ∫ t in a..P, (Iic d).indicator F t := by
  have hI : IntervalIntegrable ((Iic d).indicator F) volume a P :=
    intervalIntegrable_iff.2 ((intervalIntegrable_iff.1 hF).indicator measurableSet_Iic)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := d)
    (hI.mono_set (by rw [uIcc_of_le had, uIcc_of_le (had.trans hdP)]; exact Icc_subset_Icc le_rfl hdP))
    (hI.mono_set (by rw [uIcc_of_le hdP, uIcc_of_le (had.trans hdP)]; exact Icc_subset_Icc had le_rfl))]
  have h2 : (∫ t in d..P, (Iic d).indicator F t) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) (ae_of_all _ fun t ht => by
      rw [uIoc_of_le hdP] at ht
      exact Set.indicator_of_notMem (fun h => by simp only [mem_Iic] at h; linarith [ht.1]) _)]
    simp
  rw [h2, add_zero]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le had] at ht
  exact (Set.indicator_of_mem (show t ∈ Iic d from ht.2) _).symm

theorem prod_dvd_le_prod {S T : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hT : T ⊆ S) :
    ∏ p ∈ T, p ≤ ∏ p ∈ S, p :=
  Nat.le_of_dvd (Finset.prod_pos fun p hp => (hS p hp).pos) (Finset.prod_dvd_prod_of_subset T S _ hT)

/-- **(3c) The source-weighted sieve discrepancy identity.**  For `N ≥ 1` and every `y`,
`e^{(y−log N)/2} C_{S,N}(y−log N) − C_S(y) = q_y(1) A_S(N)/N + (1/N) ∫_1^P q_y'(t) H_{S,N}(t) dt`. -/
theorem movingCommutatorDensity_sub_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {N : ℕ}
    (hN : 0 < N) (y : ℝ) :
    movingCommutatorDensity S N y - commutatorBoundaryProfile S y =
      movingSeedProfile y 1 * roughDiscrepancy S N / N +
        (1 / N : ℝ) * ∫ t in (1 : ℝ)..(∏ p ∈ S, p : ℕ),
          Real.exp y ^ 2 * thetaCuspSeedDeriv (Real.exp y * t) * roughTailDiscrepancy S N t := by
  set q' : ℝ → ℝ := fun t => Real.exp y ^ 2 * thetaCuspSeedDeriv (Real.exp y * t)
  have hq'c : Continuous q' :=
    continuous_const.mul (continuous_thetaCuspSeedDeriv.comp (continuous_const.mul continuous_id))
  set P : ℝ := ((∏ p ∈ S, p : ℕ) : ℝ)
  have hterm : ∀ T ∈ S.powerset,
      (-1 : ℝ) ^ T.card * ((1 / (∏ p ∈ T, p : ℕ) : ℝ) *
        (((∏ p ∈ T, p : ℕ) / N : ℝ) * ∑ n ∈ Finset.Ioc (N / ∏ p ∈ T, p) N,
          movingSeedProfile y (((∏ p ∈ T, p : ℕ) / N : ℝ) * n))) -
      (-1 : ℝ) ^ T.card * ((1 / (∏ p ∈ T, p : ℕ) : ℝ) *
        ∫ t in (1 : ℝ)..(∏ p ∈ T, p : ℕ), movingSeedProfile y t) =
      (1 / N : ℝ) * ((-1 : ℝ) ^ T.card * Int.fract ((N : ℝ) / (∏ p ∈ T, p : ℕ)) * movingSeedProfile y 1 +
        ∫ t in (1 : ℝ)..P, (Iic ((∏ p ∈ T, p : ℕ) : ℝ)).indicator
          (fun t => (-1 : ℝ) ^ T.card * Int.fract (N * t / (∏ p ∈ T, p : ℕ))) t * q' t) := by
    intro T hT
    have hTS := Finset.mem_powerset.mp hT
    have hd : 0 < ∏ p ∈ T, p := Finset.prod_pos fun p hp => (hS p (hTS hp)).pos
    have hd1 : (1 : ℝ) ≤ ((∏ p ∈ T, p : ℕ) : ℝ) := by exact_mod_cast hd
    have hdP : ((∏ p ∈ T, p : ℕ) : ℝ) ≤ P := by
      simp only [P]; exact_mod_cast prod_dvd_le_prod hS hTS
    rw [← mul_sub, ← mul_sub, shell_quadrature_error (hasDerivAt_seedProfile y) hq'c hd hN,
      intervalIntegral_eq_indicator_Iic hd1 hdP (intervalIntegrable_fract_mul_div hq'c _ _ 1 P)]
    have hind : ∀ t, (Iic ((∏ p ∈ T, p : ℕ) : ℝ)).indicator
        (fun t => (-1 : ℝ) ^ T.card * Int.fract (N * t / (∏ p ∈ T, p : ℕ))) t * q' t =
        (-1 : ℝ) ^ T.card * (Iic ((∏ p ∈ T, p : ℕ) : ℝ)).indicator
          (fun t => Int.fract (N * t / (∏ p ∈ T, p : ℕ)) * q' t) t := fun t => by
      by_cases ht : t ∈ Iic ((∏ p ∈ T, p : ℕ) : ℝ)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]; ring
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]; ring
    simp_rw [hind]
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [movingCommutatorDensity_eq S hS hN, commutatorBoundaryProfile, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_add_distrib,
    ← intervalIntegral.integral_finsetSum
      (fun T _ => intervalIntegrable_indicator_fract_mul hq'c _ _ _ _ 1 P)]
  have hsum : ∀ t, ∑ T ∈ S.powerset, (Iic ((∏ p ∈ T, p : ℕ) : ℝ)).indicator
      (fun t => (-1 : ℝ) ^ T.card * Int.fract (N * t / (∏ p ∈ T, p : ℕ))) t * q' t =
      q' t * roughTailDiscrepancy S N t := fun t => by
    rw [roughTailDiscrepancy, Finset.mul_sum]
    exact Finset.sum_congr rfl fun T _ => mul_comm _ _
  simp_rw [hsum]
  rw [roughDiscrepancy, Finset.mul_sum, Finset.sum_div, mul_add]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  ring

/-! ## Uniform seed constants and the fixed-`S` moving limit -/

theorem pow_two_mul_mul_exp_neg_pi_sq_le (m : ℕ) (u : ℝ) :
    u ^ (2 * m) * Real.exp (-Real.pi * u ^ 2) ≤ m.factorial / Real.pi ^ m := by
  have hx : 0 ≤ Real.pi * u ^ 2 := by positivity
  have h := Real.pow_div_factorial_le_exp _ hx m
  have hE := Real.exp_pos (Real.pi * u ^ 2)
  have hpi : 0 < Real.pi ^ m := by positivity
  rw [show -Real.pi * u ^ 2 = -(Real.pi * u ^ 2) by ring, Real.exp_neg, pow_mul, ← div_eq_mul_inv,
    div_le_div_iff₀ hE hpi]
  have hfact : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  rw [div_le_iff₀ hfact, mul_pow] at h
  nlinarith [pow_nonneg (sq_nonneg u) m]

theorem abs_pow_mul_exp_neg_pi_sq_le {k : ℕ} (u : ℝ) :
    |u| ^ (2 * k + 1) * Real.exp (-Real.pi * u ^ 2) ≤
      Real.exp (-Real.pi * u ^ 2) + (k + 1).factorial / Real.pi ^ (k + 1) := by
  have hE := Real.exp_pos (-Real.pi * u ^ 2)
  have hE1 : Real.exp (-Real.pi * u ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
  have h := pow_two_mul_mul_exp_neg_pi_sq_le (k + 1) u
  have hsplit : |u| ^ (2 * k + 1) ≤ 1 + u ^ (2 * (k + 1)) := by
    rcases le_or_gt |u| 1 with h1 | h1
    · have : |u| ^ (2 * k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg u) h1
      nlinarith [pow_nonneg (sq_nonneg u) (k + 1), show u ^ (2 * (k + 1)) = (u ^ 2) ^ (k + 1) by
        rw [pow_mul]]
    · have : |u| ^ (2 * k + 1) ≤ |u| ^ (2 * (k + 1)) := pow_le_pow_right₀ h1.le (by omega)
      rw [pow_abs, show 2 * (k + 1) = 2 * (k + 1) from rfl] at this
      have h2 : |u| ^ (2 * (k + 1)) = u ^ (2 * (k + 1)) := by
        rw [pow_mul, sq_abs, ← pow_mul]
      rw [← pow_abs] at this
      linarith [h2 ▸ this]
  nlinarith [mul_le_mul_of_nonneg_right hsplit hE.le]

/-- `sup_u |u h(u)| < ∞`. -/
theorem exists_abs_mul_thetaCuspSeed_le : ∃ K : ℝ, ∀ u : ℝ, |u * thetaCuspSeed u| ≤ K := by
  refine ⟨2 * Real.pi * (2 * Real.pi * (1 + (2 + 1).factorial / Real.pi ^ (2 + 1)) +
    3 * (1 + (1 + 1).factorial / Real.pi ^ (1 + 1))), fun u => ?_⟩
  have hE := Real.exp_pos (-Real.pi * u ^ 2)
  have hE1 : Real.exp (-Real.pi * u ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
  have h5 := abs_pow_mul_exp_neg_pi_sq_le (k := 2) u
  have h3 := abs_pow_mul_exp_neg_pi_sq_le (k := 1) u
  rw [thetaCuspSeed, show u * (2 * Real.pi * (2 * Real.pi * u ^ 4 - 3 * u ^ 2) *
      Real.exp (-Real.pi * u ^ 2)) = 2 * Real.pi * ((2 * Real.pi * u ^ 5 - 3 * u ^ 3) *
        Real.exp (-Real.pi * u ^ 2)) by ring, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi),
    abs_mul, abs_of_pos hE]
  have hpi := Real.pi_pos
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have ha : |2 * Real.pi * u ^ 5 - 3 * u ^ 3| ≤ 2 * Real.pi * |u| ^ 5 + 3 * |u| ^ 3 := by
    refine (abs_sub _ _).trans (le_of_eq ?_)
    simp only [abs_mul, abs_pow, abs_two, abs_of_pos hpi, abs_of_pos (by norm_num : (0:ℝ) < 3)]
  calc |2 * Real.pi * u ^ 5 - 3 * u ^ 3| * Real.exp (-Real.pi * u ^ 2)
      ≤ (2 * Real.pi * |u| ^ 5 + 3 * |u| ^ 3) * Real.exp (-Real.pi * u ^ 2) :=
        mul_le_mul_of_nonneg_right ha hE.le
    _ = 2 * Real.pi * (|u| ^ (2 * 2 + 1) * Real.exp (-Real.pi * u ^ 2)) +
        3 * (|u| ^ (2 * 1 + 1) * Real.exp (-Real.pi * u ^ 2)) := by ring
    _ ≤ _ := by
      gcongr
      · linarith
      · linarith

theorem integrableOn_mul_abs_thetaCuspSeedDeriv :
    IntegrableOn (fun u : ℝ => u * |thetaCuspSeedDeriv u|) (Ioi 0) := by
  have hmaj : IntegrableOn (fun u : ℝ => 2 * Real.pi * (4 * Real.pi ^ 2 *
      (u ^ 6 * Real.exp (-Real.pi * u ^ 2)) + 14 * Real.pi * (u ^ 4 * Real.exp (-Real.pi * u ^ 2)) +
        6 * (u ^ 2 * Real.exp (-Real.pi * u ^ 2)))) (Ioi 0) :=
    ((((integrableOn_pow_mul_exp_neg_pi_sq 6).const_mul _).add
      ((integrableOn_pow_mul_exp_neg_pi_sq 4).const_mul _)).add
        ((integrableOn_pow_mul_exp_neg_pi_sq 2).const_mul _)).const_mul _
  refine hmaj.mono' ((continuous_id.mul continuous_thetaCuspSeedDeriv.abs).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu => ?_))
  have hu : 0 < u := hu
  have hE := Real.exp_pos (-Real.pi * u ^ 2)
  have hpi := Real.pi_pos
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hu, abs_abs, thetaCuspSeedDeriv, abs_mul, abs_mul,
    abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi), abs_of_pos hE]
  have ha : |-(4 * Real.pi ^ 2) * u ^ 5 + 14 * Real.pi * u ^ 3 - 6 * u| ≤
      4 * Real.pi ^ 2 * u ^ 5 + 14 * Real.pi * u ^ 3 + 6 * u := by
    rw [abs_le]; constructor <;> nlinarith [pow_pos hu 5, pow_pos hu 3]
  calc u * (2 * Real.pi * |-(4 * Real.pi ^ 2) * u ^ 5 + 14 * Real.pi * u ^ 3 - 6 * u| *
        Real.exp (-Real.pi * u ^ 2))
      ≤ u * (2 * Real.pi * (4 * Real.pi ^ 2 * u ^ 5 + 14 * Real.pi * u ^ 3 + 6 * u) *
        Real.exp (-Real.pi * u ^ 2)) := by gcongr
    _ = _ := by ring

/-- The seed moment `M = ∫_0^∞ u |h'(u)| du`. -/
def seedDerivMoment : ℝ := ∫ u in Ioi (0 : ℝ), u * |thetaCuspSeedDeriv u|

/-- `∫_1^c t |q_y'(t)| dt ≤ M` uniformly in `y` and `c ≥ 1`. -/
theorem integral_mul_abs_seedProfile_deriv_le (y : ℝ) {c : ℝ} (hc : 1 ≤ c) :
    ∫ t in (1 : ℝ)..c, t * |Real.exp y ^ 2 * thetaCuspSeedDeriv (Real.exp y * t)| ≤
      seedDerivMoment := by
  have hey := Real.exp_pos y
  have hG : ∀ t : ℝ, t * |Real.exp y ^ 2 * thetaCuspSeedDeriv (Real.exp y * t)| =
      (fun u => u * |thetaCuspSeedDeriv u| * Real.exp y) (Real.exp y * t) := fun t => by
    simp only
    rw [abs_mul, abs_of_pos (by positivity : 0 < Real.exp y ^ 2)]
    ring
  rw [intervalIntegral.integral_congr (g := fun t => (fun u => u * |thetaCuspSeedDeriv u| *
      Real.exp y) (Real.exp y * t)) fun t _ => hG t,
    intervalIntegral.integral_comp_mul_left (fun u => u * |thetaCuspSeedDeriv u| * Real.exp y)
      hey.ne', smul_eq_mul, mul_one,
    intervalIntegral.integral_mul_const, mul_comm, mul_assoc, mul_inv_cancel₀ hey.ne', mul_one,
    intervalIntegral.integral_of_le (by nlinarith)]
  refine setIntegral_mono_set integrableOn_mul_abs_thetaCuspSeedDeriv
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu =>
      mul_nonneg (le_of_lt hu) (abs_nonneg _)))
    (Eventually.of_forall fun u hu => ?_)
  exact lt_of_lt_of_le hey hu.1.le |> fun h => show u ∈ Ioi (0 : ℝ) from h

theorem abs_roughTailDiscrepancy_le (S : Finset ℕ) (N : ℕ) (t : ℝ) :
    |roughTailDiscrepancy S N t| ≤ S.powerset.card := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine Finset.sum_le_sum fun T _ => ?_
  by_cases ht : t ∈ Iic ((∏ p ∈ T, p : ℕ) : ℝ)
  · rw [Set.indicator_of_mem ht, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le
  · rw [Set.indicator_of_notMem ht, abs_zero]; exact zero_le_one

theorem abs_roughDiscrepancy_le (S : Finset ℕ) (X : ℝ) :
    |roughDiscrepancy S X| ≤ S.powerset.card := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine Finset.sum_le_sum fun T _ => ?_
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

theorem measurable_roughTailDiscrepancy (S : Finset ℕ) (N : ℕ) :
    Measurable (roughTailDiscrepancy S N) := by
  unfold roughTailDiscrepancy
  exact Finset.measurable_sum _ fun T _ =>
    (measurable_const.mul (measurable_fract_mul_div _ _)).indicator measurableSet_Iic

theorem intervalIntegrable_mul_roughTailDiscrepancy {g : ℝ → ℝ} (hg : Continuous g)
    (S : Finset ℕ) (N : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t => g t * roughTailDiscrepancy S N t) volume a b :=
  intervalIntegrable_iff.2 ((hg.intervalIntegrable a b).def'.mul_bdd
    (measurable_roughTailDiscrepancy S N).aestronglyMeasurable
    (ae_of_all _ fun t => (Real.norm_eq_abs _).trans_le (abs_roughTailDiscrepancy_le S N t)))

/-- The sieve identity bound: `|Δ_{S,N}(y)| ≤ (K |A_S(N)| + M sup_t |H_{S,N}(t)|/t ... )/N`, in the
form `|Δ| ≤ K |A_S(N)|/N + (1/N) ∫_1^P |q_y'| |H_{S,N}|`. -/
theorem abs_movingCommutatorDensity_sub_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {N : ℕ}
    (hN : 0 < N) (y : ℝ) {K : ℝ} (hK : ∀ u : ℝ, |u * thetaCuspSeed u| ≤ K) {B : ℝ}
    (hB : ∀ t, 1 ≤ t → |roughTailDiscrepancy S N t| ≤ B * t) (hB0 : 0 ≤ B) :
    |movingCommutatorDensity S N y - commutatorBoundaryProfile S y| ≤
      K * |roughDiscrepancy S N| / N + B * seedDerivMoment / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hP : (1 : ℝ) ≤ ((∏ p ∈ S, p : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun p hp => (hS p hp).pos
  have hq1 : |movingSeedProfile y 1| ≤ K := by
    have := hK (Real.exp y); rwa [movingSeedProfile, mul_one]
  have hq'c : Continuous fun t => Real.exp y ^ 2 * thetaCuspSeedDeriv (Real.exp y * t) :=
    continuous_const.mul (continuous_thetaCuspSeedDeriv.comp (continuous_const.mul continuous_id))
  have hint : |∫ t in (1 : ℝ)..(∏ p ∈ S, p : ℕ),
      Real.exp y ^ 2 * thetaCuspSeedDeriv (Real.exp y * t) * roughTailDiscrepancy S N t| ≤
        B * seedDerivMoment := by
    refine (intervalIntegral.abs_integral_le_integral_abs hP).trans ?_
    calc (∫ t in (1 : ℝ)..(∏ p ∈ S, p : ℕ),
          |Real.exp y ^ 2 * thetaCuspSeedDeriv (Real.exp y * t) * roughTailDiscrepancy S N t|)
        ≤ ∫ t in (1 : ℝ)..(∏ p ∈ S, p : ℕ),
            B * (t * |Real.exp y ^ 2 * thetaCuspSeedDeriv (Real.exp y * t)|) := by
          refine intervalIntegral.integral_mono_on hP
            (intervalIntegrable_mul_roughTailDiscrepancy hq'c S N _ _).abs
            ((continuous_id.mul hq'c.abs).intervalIntegrable _ _ |>.const_mul B) fun t ht => ?_
          rw [abs_mul, mul_comm]
          calc |roughTailDiscrepancy S N t| * |Real.exp y ^ 2 * thetaCuspSeedDeriv (Real.exp y * t)|
              ≤ (B * t) * |Real.exp y ^ 2 * thetaCuspSeedDeriv (Real.exp y * t)| :=
                mul_le_mul_of_nonneg_right (hB t ht.1) (abs_nonneg _)
            _ = _ := by ring
      _ ≤ B * seedDerivMoment := by
          rw [intervalIntegral.integral_const_mul]
          exact mul_le_mul_of_nonneg_left (integral_mul_abs_seedProfile_deriv_le y hP) hB0
  rw [movingCommutatorDensity_sub_eq S hS hN y]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_mul, abs_of_pos hNR]
    gcongr
  · rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / N), one_div_mul_eq_div]
    gcongr

/-- **(2) Moving-boundary limit.**  For a fixed finite prime set `S`, the moving shell density
converges to `C_S` uniformly on the whole line. -/
theorem tendstoUniformly_movingCommutatorDensity (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    TendstoUniformly (fun N y => movingCommutatorDensity S N y) (commutatorBoundaryProfile S)
      atTop := by
  obtain ⟨K, hK⟩ := exists_abs_mul_thetaCuspSeed_le
  set c : ℝ := (S.powerset.card : ℝ)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hlim : Tendsto (fun N : ℕ => (K * c + c * seedDerivMoment) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_ge_atTop 1] with N hN hN1 y
  rw [Real.dist_eq, abs_sub_comm]
  refine lt_of_le_of_lt ?_ hN
  have hb := abs_movingCommutatorDensity_sub_le S hS hN1 y hK (B := c)
    (fun t ht => (abs_roughTailDiscrepancy_le S N t).trans (le_mul_of_one_le_right (Nat.cast_nonneg _) ht))
    (Nat.cast_nonneg _)
  refine hb.trans ?_
  rw [add_div]
  gcongr
  exact abs_roughDiscrepancy_le S N

end

end RHTower
