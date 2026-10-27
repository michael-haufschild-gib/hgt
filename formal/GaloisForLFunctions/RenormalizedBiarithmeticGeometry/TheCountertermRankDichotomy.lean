import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheArchimedeanGermSurvivesOnItsPolarHyperplane
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheWeilPrimeKernelIsARenormalizedTorsionEnergy

/-!
# The counterterm rank dichotomy

Both places of the explicit formula are renormalized self-energies with the same universal
divergence `−log(1 − r)`:

* **the prime place** — the gcd-twisted Abel energy of torsion orbits `T_r(m, n)` on a finite set
  `S` of orders (AET). It is positive semidefinite for `r < 1`; its renormalized limit is minus
  Weil's prime kernel with the log-discriminant diagonal;
* **the archimedean place** — the Hankel family of the lattice germ `G_r(x_i + x_j)`, whose
  renormalized limit is `−ψ(x_i + x_j) − γ`.

Their counterterms differ in rank, and by scheme independence of the survival cone this is an
invariant of the two families:

* the torsion counterterm is the identity (`torsionGerm_regularized`); **every** renormalization of
  the torsion germ has survival cone `{0}` (`torsion_survivalCone_eq`), and the renormalized limit
  is indefinite on `{1, q}` for every prime power `q` (`torsionLimitForm_neg`);
* the lattice counterterm is `𝟙𝟙ᵀ`; every renormalization of the lattice germ has survival cone the
  polar-neutral hyperplane `Σ c_i = 0` (`lattice_survivalCone_eq`), where the limit is positive.

So positivity of the torsion germ is carried entirely by its divergence, while the archimedean germ
keeps it on a hyperplane (`counterterm_rank_dichotomy`). A renormalization that keeps prime-side
positivity must couple the torsion germ to a twist that lowers the rank of its counterterm.
-/

noncomputable section

open Filter Topology Finset
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

open ArithmeticEffectivityTheory

/-! ### The torsion germ as a regularized family -/

/-- The gcd-twisted torsion energy on a finite set of orders, as a matrix. -/
def torsionGerm (S : Finset ℕ) (r : ℝ) : Matrix S S ℝ :=
  Matrix.of fun m n => twistedEnergy r m n

/-- The renormalized torsion limit: `−P(m, n)` off the diagonal, `−I(n, n)/φ(n)` on it. -/
def torsionLimit (S : Finset ℕ) : Matrix S S ℝ :=
  Matrix.of fun m n => if m = n then -(orbitIntersection m m / Nat.totient m)
    else -weilPrimeKernel m n

/-- The renormalized torsion limit form on `ℕ`-indexed vectors. -/
def torsionLimitForm (S : Finset ℕ) (x : ℕ → ℝ) : ℝ :=
  -(∑ m ∈ S, ∑ n ∈ S, x m * x n * weilPrimeKernel m n) -
    ∑ n ∈ S, x n ^ 2 * (orbitIntersection n n / Nat.totient n)

/-- **The torsion germ is a regularized family with the identity as counterterm.** -/
theorem torsionGerm_regularized {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) :
    (∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ x, 0 ≤ quad (torsionGerm S r) x) ∧
      ∀ i j, Tendsto (fun r => torsionGerm S r i j - (-Real.log |1 - r|) * (1 : Matrix S S ℝ) i j)
        (𝓝[<] 1) (𝓝 (torsionLimit S i j)) := by
  classical
  refine ⟨?_, fun i j => ?_⟩
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr x
    set y : ℕ → ℝ := fun n => if h : n ∈ S then x ⟨n, h⟩ else 0
    have hy : ∀ m : S, y m = x m := fun m => by simp [y, m.2]
    have h := (weilPrimeKernel_renormalized_torsion_energy hS y).1 r hr.1.le hr.2
    rw [← sum_coe_sort S] at h
    simp_rw [← sum_coe_sort S, hy] at h
    refine h.trans_eq ?_
    simp only [quad, torsionGerm, Matrix.of_apply]
    exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by ring
  · by_cases hij : i = j
    · subst hij
      have h := (tendsto_twistedEnergy_self_add_log (hS i i.2)).mono_left
        (nhdsWithin_le_nhds (s := Set.Iio 1))
      have hval : torsionLimit S i i = -(orbitIntersection i i / Nat.totient i) := by
        simp [torsionLimit]
      rw [hval]
      refine h.congr fun r => ?_
      simp [torsionGerm]
    · have hne : (i : ℕ) ≠ j := fun h => hij (Subtype.ext h)
      have h := (tendsto_twistedEnergy_of_ne (hS i i.2) (hS j j.2) hne).mono_left
        (nhdsWithin_le_nhds (s := Set.Iio 1))
      have hval : torsionLimit S i j = -weilPrimeKernel i j := by simp [torsionLimit, hij]
      rw [hval]
      refine h.congr fun r => ?_
      simp [torsionGerm, Matrix.one_apply_ne hij]

theorem tendsto_neg_log_abs_one_sub : Tendsto (fun r : ℝ => -Real.log |1 - r|) (𝓝[<] 1) atTop := by
  have h : Tendsto (fun r : ℝ => |1 - r|) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_sub_left (1 : ℝ)).abs.tendsto (1 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt (Set.mem_Iio.mp hr)))
  exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h)

/-- **Every renormalization of the torsion germ has trivial survival cone.** -/
theorem torsion_survivalCone_eq {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) (hne : S.Nonempty)
    {t : ℝ → ℝ} {C A' : Matrix S S ℝ}
    (hC : ∀ i j, Tendsto (fun r => torsionGerm S r i j - t r * C i j) (𝓝[<] 1) (𝓝 (A' i j))) :
    survivalCone C = {0} := by
  classical
  obtain ⟨n, hn⟩ := hne
  have h1 : (1 : Matrix S S ℝ) ≠ 0 := by
    intro h
    have := congrFun (congrFun h ⟨n, hn⟩) ⟨n, hn⟩
    simp at this
  rw [survivalCone_eq_of_regularized (torsionGerm_regularized hS).2 hC
    tendsto_neg_log_abs_one_sub h1, survivalCone_one]

/-! ### The renormalized torsion limit is indefinite -/

theorem orbitIntersection_one_one : orbitIntersection 1 1 = 0 := by
  rw [orbitIntersection_self one_pos, kLogKernel]
  simp

theorem weilPrimeKernel_one_left {q : ℕ} (hq : 1 < q) :
    weilPrimeKernel 1 q = Λ q / Real.sqrt q := by
  rw [weilPrimeKernel, if_pos ⟨one_dvd q, hq.ne⟩, Nat.div_one]

theorem weilPrimeKernel_one_right {q : ℕ} (hq : 1 < q) :
    weilPrimeKernel q 1 = Λ q / Real.sqrt q := by
  have h1 : ¬ (q ∣ 1 ∧ q ≠ 1) := fun h => by
    have := Nat.le_of_dvd one_pos h.1; omega
  rw [weilPrimeKernel, if_neg h1, if_pos ⟨one_dvd q, hq.ne⟩, Nat.div_one]

theorem weilPrimeKernel_self (n : ℕ) : weilPrimeKernel n n = 0 := by
  simp [weilPrimeKernel]

/-- The limit form on the pair `{1, q}` at `x = (1, t)`. -/
theorem torsionLimitForm_pair {q : ℕ} (hq : 1 < q) {t : ℝ} {x : ℕ → ℝ} (hx1 : x 1 = 1)
    (hxq : x q = t) :
    torsionLimitForm {1, q} x =
      -(2 * t * (Λ q / Real.sqrt q)) - t ^ 2 * (orbitIntersection q q / Nat.totient q) := by
  have h1q : (1 : ℕ) ∉ ({q} : Finset ℕ) := by simp; omega
  simp only [torsionLimitForm, sum_insert h1q, sum_singleton, hx1, hxq,
    weilPrimeKernel_self, weilPrimeKernel_one_left hq, weilPrimeKernel_one_right hq,
    orbitIntersection_one_one, Nat.totient_one]
  ring

/-- **The renormalized torsion limit is indefinite**: for every prime power `q` there is a vector on
`{1, q}` where the limit form is negative. Weil's prime kernel couples `1` to `q` with weight
`Λ(q)/√q > 0`, while the orbit of order `1` has zero self-intersection. -/
theorem torsionLimitForm_neg {q : ℕ} (hq : IsPrimePow q) :
    ∃ x : ℕ → ℝ, torsionLimitForm {1, q} x < 0 := by
  have hq1 : 1 < q := hq.one_lt
  set P : ℝ := Λ q / Real.sqrt q
  have hP : 0 < P := div_pos (ArithmeticFunction.vonMangoldt_pos_iff.mpr hq)
    (Real.sqrt_pos.mpr (by exact_mod_cast (zero_lt_one.trans hq1)))
  set c : ℝ := orbitIntersection q q / Nat.totient q
  set t : ℝ := P / (|c| + 1)
  have ht : 0 < t := div_pos hP (by positivity)
  have htc : t * |c| < P := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg c]
  refine ⟨fun n => if n = 1 then 1 else t, ?_⟩
  rw [torsionLimitForm_pair hq1 (t := t) (by simp) (by simp [hq1.ne'])]
  have hc : -(t ^ 2 * c) ≤ t ^ 2 * |c| := by
    nlinarith [neg_abs_le c, sq_nonneg t]
  nlinarith

/-! ### The archimedean side and the dichotomy -/

/-- **Every renormalization of the lattice germ has the polar-neutral hyperplane as survival
cone.** -/
theorem lattice_survivalCone_eq {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ} (hx : ∀ i, 0 < x i)
    {t : ℝ → ℝ} {C A' : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ i j, Tendsto (fun r => latticeHankel x r i j - t r * C i j) (𝓝[<] 1) (𝓝 (A' i j))) :
    survivalCone C = {c | ∑ i, c i = 0} := by
  have hB0 : latticeCounterterm n ≠ 0 := by
    intro h
    have := congrFun (congrFun h ⟨0, hn⟩) ⟨0, hn⟩
    simp [latticeCounterterm, Matrix.vecMulVec_apply] at this
  have hs : Tendsto (fun r : ℝ => -Real.log (1 - r)) (𝓝[<] 1) atTop := by
    refine tendsto_neg_log_abs_one_sub.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [abs_of_pos (sub_pos.mpr hr)]
  rw [survivalCone_eq_of_regularized (latticeHankel_regularized hx).2 hC hs hB0]
  ext c
  rw [latticeCounterterm, mem_survivalCone_vecMulVec_iff]
  simp

/-- **The counterterm rank dichotomy.** The torsion germ (prime place) has the identity as
counterterm: under every renormalization nothing survives, and its renormalized limit is
indefinite at every prime power. The lattice germ (archimedean place) has a rank-one counterterm:
under every renormalization the polar-neutral hyperplane survives, the limit is positive there, and
it is not positive off it. -/
theorem counterterm_rank_dichotomy :
    (∀ (S : Finset ℕ), (∀ n ∈ S, 0 < n) → S.Nonempty →
      ∀ (t : ℝ → ℝ) (C A' : Matrix S S ℝ),
        (∀ i j, Tendsto (fun r => torsionGerm S r i j - t r * C i j) (𝓝[<] 1) (𝓝 (A' i j))) →
          survivalCone C = {0}) ∧
    (∀ q : ℕ, IsPrimePow q → ∃ x : ℕ → ℝ, torsionLimitForm {1, q} x < 0) ∧
    (∀ (n : ℕ) (x : Fin n → ℝ), 0 < n → (∀ i, 0 < x i) →
      ∀ (t : ℝ → ℝ) (C A' : Matrix (Fin n) (Fin n) ℝ),
        (∀ i j, Tendsto (fun r => latticeHankel x r i j - t r * C i j) (𝓝[<] 1) (𝓝 (A' i j))) →
          survivalCone C = {c | ∑ i, c i = 0}) ∧
    (∀ (n : ℕ) (x : Fin n → ℝ), (∀ i, 0 < x i) → ∀ c : Fin n → ℝ, ∑ i, c i = 0 →
      0 ≤ ∑ i, ∑ j, c i * c j * (-(Complex.digamma ((x i + x j : ℝ) : ℂ)).re)) ∧
    (¬ ∀ (n : ℕ) (x : Fin n → ℝ), (∀ i, 0 < x i) → ∀ c, 0 ≤ quad (latticeHankelLimit x) c) :=
  ⟨fun _ hS hne _ _ _ hC => torsion_survivalCone_eq hS hne hC,
    fun _ hq => torsionLimitForm_neg hq,
    fun _ _ hn hx _ _ _ hC => lattice_survivalCone_eq hn hx hC,
    fun _ _ hx _ hc => neg_digamma_hankel_nonneg hx hc,
    not_nonneg_latticeGermLimit⟩

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
