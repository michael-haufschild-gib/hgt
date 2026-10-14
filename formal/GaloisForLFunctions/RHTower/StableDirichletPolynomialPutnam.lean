import GaloisForLFunctions.RHTower.HerglotzDirichletCarrierRigidity

/-!
# Stable Dirichlet polynomials have critical zeros off the zeros of ζ

Let `n₁, …, n_k ≥ 2` be integers and `Q(z) = Σ_{S ⊆ {1,…,k}} q_S Π_{j∈S} z_j` a real multiaffine
polynomial with `q_∅ ≠ 0` which is

* *stable*: `Q(z) ≠ 0` whenever every `|z_j| < 1`;
* *self-reciprocal*: `q_{Sᶜ} = q_S`;
* *small at `3/2`*: `Σ_{S ≠ ∅} |q_S/q_∅| Π_{j∈S} n_j^{−1} < 1`.

Put `P(s) = Q(n₁^{½−s}, …, n_k^{½−s})`.

**Theorem** (`exists_zero_stableDirichlet_riemannZeta_ne_zero`).  There is a real `t` with
`P(½ + it) = 0` and `ζ(½ + it) ≠ 0`.

For `k = 1` this is a form of Putnam's theorem on progressions of zeros; for `k ≥ 2` the zero sets
`{t : P(½ + it) = 0}` are quasi-periodic, e.g. `cos(½t log 6) + a cos(½t log(3/2)) = 0` for
`Q = 1 + a(z₁ + z₂) + z₁z₂`, `n = (2, 3)`, `|a| < 1`.

**Proof.**  `H(s) = Σ_j log n_j (½ − z_j∂_jQ/Q)` at `z_j = n_j^{½−s}` is holomorphic with `Re H ≥ 0`
on `Re s > ½`: stability makes `Q = A + z_jB` with `|B| ≤ |A|`, so `Re(z_jB/(A + z_jB)) ≤ ½`.  On
the critical line self-reciprocity gives `|B| = |A|`, so `Re H = 0` wherever `P ≠ 0`.  Expanding
`1/Q` geometrically, `H` is an absolutely convergent Dirichlet series on `Re s ≥ 3/2` with constant
term `½ Σ_j log n_j > 0`.  If every critical zero of `P` were a zero of `ζ`, the Herglotz carrier
rigidity theorem (`eq_zero_of_herglotz_dirichlet_criticalCarrier`) would force that constant to
vanish.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace RHTower.StablePutnam

open Finset

variable {k : ℕ}

/-! ## Multiaffine polynomials -/

/-- The monomial `z^S = Π_{i ∈ S} z_i`. -/
def mono (S : Finset (Fin k)) (z : Fin k → ℂ) : ℂ := ∏ i ∈ S, z i

/-- A real multiaffine polynomial `Q(z) = Σ_S q_S z^S`. -/
def maQ (q : Finset (Fin k) → ℝ) (z : Fin k → ℂ) : ℂ := ∑ S, (q S : ℂ) * mono S z

/-- Its `j`-th Euler part `z_j ∂_j Q = Σ_{S ∋ j} q_S z^S`. -/
def maE (q : Finset (Fin k) → ℝ) (j : Fin k) (z : Fin k → ℂ) : ℂ :=
  ∑ S ∈ univ.filter (fun S => j ∈ S), (q S : ℂ) * mono S z

/-- The part `A_j = Σ_{S ∌ j} q_S z^S`, free of `z_j`. -/
def maA (q : Finset (Fin k) → ℝ) (j : Fin k) (z : Fin k → ℂ) : ℂ :=
  ∑ S ∈ univ.filter (fun S => j ∉ S), (q S : ℂ) * mono S z

/-- The coefficient `B_j = Σ_{S ∋ j} q_S z^{S ∖ j}` of `z_j`. -/
def maB (q : Finset (Fin k) → ℝ) (j : Fin k) (z : Fin k → ℂ) : ℂ :=
  ∑ S ∈ univ.filter (fun S => j ∈ S), (q S : ℂ) * mono (S.erase j) z

theorem maQ_eq (q : Finset (Fin k) → ℝ) (j : Fin k) (z : Fin k → ℂ) :
    maQ q z = maA q j z + maE q j z := by
  unfold maQ maA maE
  rw [add_comm, sum_filter_add_sum_filter_not]

theorem maE_eq (q : Finset (Fin k) → ℝ) (j : Fin k) (z : Fin k → ℂ) :
    maE q j z = z j * maB q j z := by
  unfold maE maB
  rw [mul_sum]
  refine sum_congr rfl fun S hS => ?_
  have hj : j ∈ S := (mem_filter.mp hS).2
  unfold mono
  rw [← mul_prod_erase S z hj]
  ring

theorem mono_update {S : Finset (Fin k)} {j : Fin k} (hj : j ∉ S) (z : Fin k → ℂ) (w : ℂ) :
    mono S (Function.update z j w) = mono S z := by
  unfold mono
  refine prod_congr rfl fun i hi => ?_
  have hij : i ≠ j := fun h => hj (by rw [← h]; exact hi)
  rw [Function.update_of_ne hij]

theorem maA_update (q : Finset (Fin k) → ℝ) (j : Fin k) (z : Fin k → ℂ) (w : ℂ) :
    maA q j (Function.update z j w) = maA q j z := by
  unfold maA
  refine sum_congr rfl fun S hS => ?_
  rw [mono_update (mem_filter.mp hS).2]

theorem maB_update (q : Finset (Fin k) → ℝ) (j : Fin k) (z : Fin k → ℂ) (w : ℂ) :
    maB q j (Function.update z j w) = maB q j z := by
  unfold maB
  refine sum_congr rfl fun S _ => ?_
  rw [mono_update (Finset.notMem_erase j S)]

theorem maQ_update (q : Finset (Fin k) → ℝ) (j : Fin k) (z : Fin k → ℂ) (w : ℂ) :
    maQ q (Function.update z j w) = maA q j z + w * maB q j z := by
  rw [maQ_eq q j, maE_eq, maA_update, maB_update, Function.update_self]

/-! ## Stability and the Herglotz inequality -/

/-- `Q` has no zeros in the open unit polydisc. -/
def Stable (q : Finset (Fin k) → ℝ) : Prop := ∀ z : Fin k → ℂ, (∀ i, ‖z i‖ < 1) → maQ q z ≠ 0

theorem maA_ne_zero_and_norm_le {q : Finset (Fin k) → ℝ} (hst : Stable q) {z : Fin k → ℂ}
    (hz : ∀ i, ‖z i‖ < 1) (j : Fin k) : maA q j z ≠ 0 ∧ ‖maB q j z‖ ≤ ‖maA q j z‖ := by
  have hupd : ∀ w : ℂ, ‖w‖ < 1 → maA q j z + w * maB q j z ≠ 0 := by
    intro w hw
    rw [← maQ_update]
    refine hst _ fun i => ?_
    by_cases hi : i = j
    · subst hi
      rw [Function.update_self]
      exact hw
    · rw [Function.update_of_ne hi]
      exact hz i
  have hA : maA q j z ≠ 0 := by simpa using hupd 0 (by simp)
  refine ⟨hA, ?_⟩
  by_contra hlt
  push Not at hlt
  have hB : maB q j z ≠ 0 := fun h => by
    rw [h, norm_zero] at hlt
    exact absurd hlt (not_lt.mpr (norm_nonneg _))
  apply hupd (-(maA q j z / maB q j z))
  · rw [norm_neg, norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hB)).mpr hlt
  · field_simp
    ring

theorem re_div_one_add_le {w : ℂ} (hw : ‖w‖ ≤ 1) (h : 1 + w ≠ 0) :
    (w / (1 + w)).re ≤ 1 / 2 := by
  have hn : 0 < normSq (1 + w) := normSq_pos.mpr h
  have hw2 : w.re ^ 2 + w.im ^ 2 ≤ 1 := by
    have h1 := Complex.sq_norm w
    rw [normSq_apply] at h1
    nlinarith [norm_nonneg w]
  rw [div_re, ← add_div, div_le_iff₀ hn, normSq_apply]
  simp only [add_re, one_re, add_im, one_im, zero_add]
  nlinarith

theorem re_div_one_add_eq {w : ℂ} (hw : ‖w‖ = 1) (h : 1 + w ≠ 0) :
    (w / (1 + w)).re = 1 / 2 := by
  have hn : 0 < normSq (1 + w) := normSq_pos.mpr h
  have hw2 : w.re ^ 2 + w.im ^ 2 = 1 := by
    have h1 := Complex.sq_norm w
    rw [normSq_apply, hw] at h1
    nlinarith
  rw [div_re, ← add_div, div_eq_iff hn.ne', normSq_apply]
  simp only [add_re, one_re, add_im, one_im, zero_add]
  nlinarith

theorem re_maE_div_maQ_le {q : Finset (Fin k) → ℝ} (hst : Stable q) {z : Fin k → ℂ}
    (hz : ∀ i, ‖z i‖ < 1) (j : Fin k) : (maE q j z / maQ q z).re ≤ 1 / 2 := by
  obtain ⟨hA, hBA⟩ := maA_ne_zero_and_norm_le hst hz j
  set w := z j * maB q j z / maA q j z with hw
  have hQ : maQ q z = maA q j z * (1 + w) := by
    rw [maQ_eq q j, maE_eq, hw]
    field_simp
  have hE : maE q j z = maA q j z * w := by
    rw [maE_eq, hw]
    field_simp
  have h1w : 1 + w ≠ 0 := fun h => hst z hz (by rw [hQ, h, mul_zero])
  rw [hQ, hE, mul_div_mul_left _ _ hA]
  refine re_div_one_add_le ?_ h1w
  rw [hw, norm_div, norm_mul, div_le_one (norm_pos_iff.mpr hA)]
  calc ‖z j‖ * ‖maB q j z‖ ≤ 1 * ‖maB q j z‖ :=
        mul_le_mul_of_nonneg_right (hz j).le (norm_nonneg _)
    _ ≤ ‖maA q j z‖ := by rw [one_mul]; exact hBA

/-! ## Self-reciprocity on the torus -/

/-- Self-reciprocity `q_{Sᶜ} = q_S`. -/
def SelfRecip (q : Finset (Fin k) → ℝ) : Prop := ∀ S, q Sᶜ = q S

theorem maB_eq_torus {q : Finset (Fin k) → ℝ} (hq : SelfRecip q) {z : Fin k → ℂ}
    (hz : ∀ i, ‖z i‖ = 1) (j : Fin k) :
    maB q j z = mono (univ.erase j) z * conj (maA q j z) := by
  have hinv : ∀ i, conj (z i) = (z i)⁻¹ := fun i => by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz i]
    simp
  have hne : ∀ i, z i ≠ 0 := fun i h => by
    have := hz i
    rw [h, norm_zero] at this
    exact zero_ne_one this
  unfold maA maB
  rw [map_sum, mul_sum]
  symm
  refine sum_nbij' (fun S => Sᶜ) (fun T => Tᶜ) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    have h1 : j ∉ S := (Finset.mem_filter.mp hS).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_compl.mpr h1⟩
  · intro T hT
    have h1 : j ∈ T := (Finset.mem_filter.mp hT).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_compl.mp h) h1⟩
  · intro S _
    simp
  · intro T _
    simp
  · intro S hS
    have hjS : j ∉ S := (Finset.mem_filter.mp hS).2
    rw [map_mul, Complex.conj_ofReal, hq S]
    have hsub : S ⊆ univ.erase j := fun i hi =>
      Finset.mem_erase.mpr ⟨fun h => hjS (by rw [← h]; exact hi), Finset.mem_univ i⟩
    have hcm : conj (mono S z) = (mono S z)⁻¹ := by
      unfold mono
      rw [map_prod, ← prod_inv_distrib]
      exact prod_congr rfl fun i _ => hinv i
    have hset : Sᶜ.erase j = (univ.erase j) \ S := by
      ext i
      simp only [Finset.mem_erase, Finset.mem_compl, Finset.mem_sdiff, Finset.mem_univ, and_true]
    have hprod := prod_sdiff (f := z) hsub
    have hmS : mono S z ≠ 0 := prod_ne_zero_iff.mpr fun i _ => hne i
    rw [hcm, hset]
    unfold mono at hmS ⊢
    rw [← hprod]
    field_simp

theorem norm_maB_eq_torus {q : Finset (Fin k) → ℝ} (hq : SelfRecip q) {z : Fin k → ℂ}
    (hz : ∀ i, ‖z i‖ = 1) (j : Fin k) : ‖maB q j z‖ = ‖maA q j z‖ := by
  rw [maB_eq_torus hq hz j, norm_mul, Complex.norm_conj]
  have : ‖mono (univ.erase j) z‖ = 1 := by
    unfold mono
    rw [norm_prod]
    exact prod_eq_one fun i _ => hz i
  rw [this, one_mul]

theorem re_maE_div_maQ_torus {q : Finset (Fin k) → ℝ} (hq : SelfRecip q) {z : Fin k → ℂ}
    (hz : ∀ i, ‖z i‖ = 1) (hQ : maQ q z ≠ 0) (j : Fin k) :
    (maE q j z / maQ q z).re = 1 / 2 := by
  have hA : maA q j z ≠ 0 := by
    intro hA0
    have hB : maB q j z = 0 := by
      rw [← norm_eq_zero, norm_maB_eq_torus hq hz, hA0, norm_zero]
    exact hQ (by rw [maQ_eq q j, maE_eq, hA0, hB, mul_zero, add_zero])
  set w := z j * maB q j z / maA q j z with hw
  have hQ' : maQ q z = maA q j z * (1 + w) := by
    rw [maQ_eq q j, maE_eq, hw]
    field_simp
  have hE : maE q j z = maA q j z * w := by
    rw [maE_eq, hw]
    field_simp
  have h1w : 1 + w ≠ 0 := fun h => hQ (by rw [hQ', h, mul_zero])
  rw [hQ', hE, mul_div_mul_left _ _ hA]
  refine re_div_one_add_eq ?_ h1w
  rw [hw, norm_div, norm_mul, hz j, one_mul, norm_maB_eq_torus hq hz,
    div_self (norm_ne_zero_iff.mpr hA)]

/-! ## The Dirichlet point and the Herglotz function -/

/-- The point `z_j(s) = n_j^{½ − s}`. -/
def zpt (n : Fin k → ℕ) (s : ℂ) : Fin k → ℂ := fun j => (n j : ℂ) ^ ((1 / 2 : ℂ) - s)

theorem norm_zpt {n : Fin k → ℕ} (hn : ∀ j, 2 ≤ n j) (s : ℂ) (j : Fin k) :
    ‖zpt n s j‖ = (n j : ℝ) ^ (1 / 2 - s.re) := by
  unfold zpt
  rw [Complex.norm_natCast_cpow_of_pos (by have := hn j; omega)]
  simp

theorem norm_zpt_lt_one {n : Fin k → ℕ} (hn : ∀ j, 2 ≤ n j) {s : ℂ} (hs : 1 / 2 < s.re)
    (j : Fin k) : ‖zpt n s j‖ < 1 := by
  rw [norm_zpt hn]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (show 1 < n j by have := hn j; omega))
    (by linarith)

theorem norm_zpt_critical {n : Fin k → ℕ} (hn : ∀ j, 2 ≤ n j) (t : ℝ) (j : Fin k) :
    ‖zpt n ((1 / 2 : ℂ) + t * I) j‖ = 1 := by
  rw [norm_zpt hn]
  simp

theorem differentiable_zpt {n : Fin k → ℕ} (hn : ∀ j, 2 ≤ n j) (j : Fin k) :
    Differentiable ℂ fun s => zpt n s j := fun s =>
  ((differentiableAt_const _).sub differentiableAt_id).const_cpow
    (Or.inl (by have := hn j; exact_mod_cast (show n j ≠ 0 by omega)))

theorem differentiable_mono_zpt {n : Fin k → ℕ} (hn : ∀ j, 2 ≤ n j) (S : Finset (Fin k)) :
    Differentiable ℂ fun s => mono S (zpt n s) := by
  unfold mono
  exact Differentiable.fun_finsetProd fun i _ => differentiable_zpt hn i

theorem differentiable_maQ_zpt {n : Fin k → ℕ} (hn : ∀ j, 2 ≤ n j) (q : Finset (Fin k) → ℝ) :
    Differentiable ℂ fun s => maQ q (zpt n s) := by
  unfold maQ
  exact Differentiable.fun_sum fun S _ => (differentiable_mono_zpt hn S).const_mul _

theorem differentiable_maE_zpt {n : Fin k → ℕ} (hn : ∀ j, 2 ≤ n j) (q : Finset (Fin k) → ℝ)
    (j : Fin k) : Differentiable ℂ fun s => maE q j (zpt n s) := by
  unfold maE
  exact Differentiable.fun_sum fun S _ => (differentiable_mono_zpt hn S).const_mul _

/-- `H(s) = Σ_j log n_j (½ − z_j∂_jQ/Q)` at `z = (n_j^{½−s})`. -/
def stableH (q : Finset (Fin k) → ℝ) (n : Fin k → ℕ) (s : ℂ) : ℂ :=
  ∑ j, (Real.log (n j) : ℂ) * (1 / 2 - maE q j (zpt n s) / maQ q (zpt n s))

theorem re_stableH (q : Finset (Fin k) → ℝ) (n : Fin k → ℕ) (s : ℂ) :
    (stableH q n s).re =
      ∑ j, Real.log (n j) * (1 / 2 - (maE q j (zpt n s) / maQ q (zpt n s)).re) := by
  unfold stableH
  rw [Complex.re_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [Complex.re_ofReal_mul, Complex.sub_re]
  norm_num

theorem re_stableH_nonneg {q : Finset (Fin k) → ℝ} (hst : Stable q) {n : Fin k → ℕ}
    (hn : ∀ j, 2 ≤ n j) {s : ℂ} (hs : 1 / 2 < s.re) : 0 ≤ (stableH q n s).re := by
  rw [re_stableH]
  refine sum_nonneg fun j _ => mul_nonneg (Real.log_nonneg (by exact_mod_cast
    (show 1 ≤ n j by have := hn j; omega))) ?_
  have := re_maE_div_maQ_le hst (norm_zpt_lt_one hn hs) j
  linarith

theorem differentiableAt_stableH {q : Finset (Fin k) → ℝ} {n : Fin k → ℕ} (hn : ∀ j, 2 ≤ n j)
    {s : ℂ} (hQ : maQ q (zpt n s) ≠ 0) : DifferentiableAt ℂ (stableH q n) s := by
  have h : stableH q n = fun s => ∑ j, (Real.log (n j) : ℂ) *
      (1 / 2 - maE q j (zpt n s) / maQ q (zpt n s)) := rfl
  rw [h]
  refine DifferentiableAt.fun_sum fun j _ => (differentiableAt_const _).mul
    ((differentiableAt_const _).sub ?_)
  exact ((differentiable_maE_zpt hn q j) s).div ((differentiable_maQ_zpt hn q) s) hQ

theorem differentiableOn_stableH {q : Finset (Fin k) → ℝ} (hst : Stable q) {n : Fin k → ℕ}
    (hn : ∀ j, 2 ≤ n j) : DifferentiableOn ℂ (stableH q n) {s : ℂ | 1 / 2 < s.re} :=
  fun _ hs => (differentiableAt_stableH hn (hst _ (norm_zpt_lt_one hn hs))).differentiableWithinAt

/-- On the critical line, away from the zeros of `P`, the real part of `H` vanishes. -/
theorem tendsto_re_stableH_critical {q : Finset (Fin k) → ℝ} (hq : SelfRecip q)
    {n : Fin k → ℕ} (hn : ∀ j, 2 ≤ n j) {t : ℝ}
    (hP : maQ q (zpt n ((1 / 2 : ℂ) + t * I)) ≠ 0) :
    Tendsto (fun s => (stableH q n s).re) (𝓝[{s : ℂ | 1 / 2 < s.re}] ((1 / 2 : ℂ) + t * I))
      (𝓝 0) := by
  have hc := (differentiableAt_stableH hn hP).continuousAt
  have h0 : (stableH q n ((1 / 2 : ℂ) + t * I)).re = 0 := by
    rw [re_stableH]
    refine sum_eq_zero fun j _ => ?_
    rw [re_maE_div_maQ_torus hq (norm_zpt_critical hn t) hP j]
    ring
  have := (Complex.continuous_re.tendsto _).comp hc
  rw [h0] at this
  exact this.mono_left nhdsWithin_le_nhds

/-! ## Grouping a family by frequency -/

theorem tsum_fiber_eq_term {ι : Type*} {c : ι → ℝ} {m : ι → ℕ} (hm : ∀ x, 1 ≤ m x) (s : ℂ)
    (j : ℕ) : (∑' x : m ⁻¹' {j}, (c x : ℂ) * (m x : ℂ) ^ (-s)) =
      LSeries.term (fun j => ((∑' x : m ⁻¹' {j}, c x : ℝ) : ℂ)) s j := by
  have hcongr : (fun x : m ⁻¹' {j} => (c x : ℂ) * (m x : ℂ) ^ (-s)) =
      fun x : m ⁻¹' {j} => (c x : ℂ) * (j : ℂ) ^ (-s) := by
    funext x
    rw [show m x = j from x.2]
  rw [hcongr, tsum_mul_right, ← Complex.ofReal_tsum]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hempty : IsEmpty (m ⁻¹' {0}) := ⟨fun x => by
      have h1 := hm x.1
      have h2 : m x.1 = 0 := x.2
      omega⟩
    rw [LSeries.term_zero, tsum_empty, Complex.ofReal_zero, zero_mul]
  · rw [LSeries.term_of_ne_zero hj.ne', Complex.cpow_neg, div_eq_mul_inv]

theorem LSeriesSummable_of_family {ι : Type*} {c : ι → ℝ} {m : ι → ℕ} {σ₀ : ℝ}
    (hs : Summable fun x => |c x| * (m x : ℝ) ^ (-σ₀)) :
    LSeriesSummable (fun j => ((∑' x : m ⁻¹' {j}, c x : ℝ) : ℂ)) σ₀ := by
  have hR := hs.hasSum.tsum_fiberwise m
  have hnorm : Summable fun j : ℕ =>
      ‖LSeries.term (fun j => ((∑' x : m ⁻¹' {j}, c x : ℝ) : ℂ)) (σ₀ : ℂ) j‖ := by
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hR.summable
    rw [LSeries.norm_term_eq]
    split_ifs with hj0
    · exact tsum_nonneg fun _ => by positivity
    · have hjpos : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj0
      have hfs : (∑' x : m ⁻¹' {j}, |c x| * (m x : ℝ) ^ (-σ₀)) =
          (∑' x : m ⁻¹' {j}, |c x|) * (j : ℝ) ^ (-σ₀) := by
        rw [← tsum_mul_right]
        refine tsum_congr fun x => ?_
        rw [show m x = j from x.2]
      rw [hfs, Complex.norm_real, Real.norm_eq_abs]
      have hsub : Summable fun x : m ⁻¹' {j} => |c x| := by
        have := hs.subtype (m ⁻¹' {j})
        refine (this.mul_right ((j : ℝ) ^ σ₀)).congr fun x => ?_
        simp only [Function.comp]
        rw [show m x = j from x.2, mul_assoc, ← Real.rpow_add hjpos, neg_add_cancel,
          Real.rpow_zero, mul_one]
      have habs : |∑' x : m ⁻¹' {j}, c x| ≤ ∑' x : m ⁻¹' {j}, |c x| := by
        have hs' : Summable fun x : m ⁻¹' {j} => ‖c x‖ := by
          simpa only [Real.norm_eq_abs] using hsub
        have := norm_tsum_le_tsum_norm hs'
        simpa only [Real.norm_eq_abs] using this
      have hre : ((σ₀ : ℂ)).re = σ₀ := Complex.ofReal_re σ₀
      rw [hre, div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg j)]
      exact mul_le_mul_of_nonneg_right habs (by positivity)
  exact hnorm.of_norm

/-- **Grouping by frequency.**  An absolutely summable family `c_x m_x^{−s}` with integer
frequencies `m_x ≥ 1` is the Dirichlet series of `a(m) = Σ_{m_x = m} c_x`. -/
theorem hasSum_LSeries_of_family {ι : Type*} {c : ι → ℝ} {m : ι → ℕ} (hm : ∀ x, 1 ≤ m x)
    {σ₀ : ℝ} (hs : Summable fun x => |c x| * (m x : ℝ) ^ (-σ₀)) {s : ℂ} (hs0 : σ₀ ≤ s.re) :
    HasSum (fun x => (c x : ℂ) * (m x : ℂ) ^ (-s))
      (LSeries (fun j => ((∑' x : m ⁻¹' {j}, c x : ℝ) : ℂ)) s) := by
  have hsumF : Summable fun x => (c x : ℂ) * (m x : ℂ) ^ (-s) := by
    refine Summable.of_norm_bounded hs fun x => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_natCast_cpow_of_pos (by have := hm x; omega)]
    simp only [neg_re]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hm x) (by linarith)) (abs_nonneg _)
  have hF := hsumF.hasSum.tsum_fiberwise m
  simp_rw [tsum_fiber_eq_term hm s] at hF
  have hL : LSeries (fun j => ((∑' x : m ⁻¹' {j}, c x : ℝ) : ℂ)) s =
      ∑' x, (c x : ℂ) * (m x : ℂ) ^ (-s) := by
    rw [LSeries, hF.tsum_eq]
  rw [hL]
  exact hsumF.hasSum

/-! ## The Dirichlet expansion of `H` -/

/-- `N_S = Π_{i ∈ S} n_i`. -/
def Nprod (n : Fin k → ℕ) (S : Finset (Fin k)) : ℕ := ∏ i ∈ S, n i

theorem Nprod_pos {n : Fin k → ℕ} (hn : ∀ j, 2 ≤ n j) (S : Finset (Fin k)) : 0 < Nprod n S :=
  prod_pos fun i _ => by have := hn i; omega

theorem Nprod_eq_one {n : Fin k → ℕ} (hn : ∀ j, 2 ≤ n j) {S : Finset (Fin k)}
    (h : Nprod n S = 1) : S = ∅ := by
  by_contra hS
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
  have hdvd : n i ∣ Nprod n S := Finset.dvd_prod_of_mem n hi
  rw [h] at hdvd
  have := Nat.le_of_dvd one_pos hdvd
  have := hn i
  omega

theorem natCast_prod_cpow {ι : Type*} (s : Finset ι) (f : ι → ℕ) (x : ℂ) :
    (((∏ i ∈ s, f i : ℕ) : ℂ)) ^ x = ∏ i ∈ s, ((f i : ℕ) : ℂ) ^ x := by
  classical
  refine Finset.induction_on s (by simp) fun a s ha ih => ?_
  rw [prod_insert ha, prod_insert ha, Nat.cast_mul, natCast_mul_natCast_cpow, ih]

theorem mono_zpt (n : Fin k → ℕ) (S : Finset (Fin k)) (s : ℂ) :
    mono S (zpt n s) = ((Nprod n S : ℕ) : ℂ) ^ ((1 / 2 : ℂ) - s) := by
  unfold mono zpt Nprod
  rw [natCast_prod_cpow]

theorem norm_mono_zpt_le {n : Fin k → ℕ} (hn : ∀ j, 2 ≤ n j) (S : Finset (Fin k)) {s : ℂ}
    (hs : 3 / 2 ≤ s.re) : ‖mono S (zpt n s)‖ ≤ ((Nprod n S : ℕ) : ℝ)⁻¹ := by
  have hpos : (1 : ℝ) ≤ Nprod n S := by exact_mod_cast Nprod_pos hn S
  rw [mono_zpt, Complex.norm_natCast_cpow_of_pos (Nprod_pos hn S), ← Real.rpow_neg_one]
  refine Real.rpow_le_rpow_of_exponent_le hpos ?_
  simp only [sub_re, div_ofNat_re, one_re]
  linarith

/-- The geometric coefficients `−q_S/q_∅`, and `0` at `S = ∅`. -/
def gq (q : Finset (Fin k) → ℝ) (S : Finset (Fin k)) : ℝ := if S = ∅ then 0 else -(q S / q ∅)

theorem maQ_eq_geom (q : Finset (Fin k) → ℝ) (hq0 : q ∅ ≠ 0) (z : Fin k → ℂ) :
    maQ q z = q ∅ * (1 - ∑ S, (gq q S : ℂ) * mono S z) := by
  have hq0' : (q ∅ : ℂ) ≠ 0 := by exact_mod_cast hq0
  have h1 : maQ q z = ∑ S, ((if S = ∅ then (q ∅ : ℂ) else 0) +
      (if S = ∅ then 0 else (q S : ℂ) * mono S z)) := by
    unfold maQ
    refine sum_congr rfl fun S _ => ?_
    by_cases hS : S = ∅
    · subst hS
      simp [mono]
    · simp [hS]
  have h2 : (q ∅ : ℂ) * (1 - ∑ S, (gq q S : ℂ) * mono S z) =
      (q ∅ : ℂ) + ∑ S, (if S = ∅ then 0 else (q S : ℂ) * mono S z) := by
    rw [mul_sub, mul_one, mul_sum, sub_eq_add_neg, ← sum_neg_distrib]
    congr 1
    refine sum_congr rfl fun S _ => ?_
    unfold gq
    by_cases hS : S = ∅
    · simp [hS]
    · simp only [if_neg hS]
      push_cast
      field_simp
  rw [h1, sum_add_distrib, h2]
  simp

/-- The expansion index `(j, T, ℓ, p)`. -/
abbrev ExpIdx (k : ℕ) := Fin k × Finset (Fin k) × (Σ ℓ : ℕ, Fin ℓ → Finset (Fin k))

/-- The frequency `N_T Π_r N_{p_r}` of an expansion term. -/
def expFreq (n : Fin k → ℕ) (x : ExpIdx k) : ℕ := Nprod n x.2.1 * ∏ r, Nprod n (x.2.2.2 r)

/-- The `T`-coefficient `[j ∈ T] q_T/q_∅`. -/
def coefT (q : Finset (Fin k) → ℝ) (j : Fin k) (T : Finset (Fin k)) : ℝ :=
  (if j ∈ T then q T else 0) / q ∅

/-- The coefficient of an expansion term. -/
def expCoef (q : Finset (Fin k) → ℝ) (n : Fin k → ℕ) (x : ExpIdx k) : ℝ :=
  -Real.log (n x.1) * coefT q x.1 x.2.1 * (∏ r, gq q (x.2.2.2 r)) * Real.sqrt (expFreq n x)

theorem expFreq_pos {n : Fin k → ℕ} (hn : ∀ j, 2 ≤ n j) (x : ExpIdx k) : 0 < expFreq n x :=
  Nat.mul_pos (Nprod_pos hn _) (prod_pos fun _ _ => Nprod_pos hn _)

theorem expTerm_eq {n : Fin k → ℕ} (hn : ∀ j, 2 ≤ n j) (q : Finset (Fin k) → ℝ) (x : ExpIdx k)
    (s : ℂ) : (expCoef q n x : ℂ) * (expFreq n x : ℂ) ^ (-s) =
      -(Real.log (n x.1) : ℂ) * ((coefT q x.1 x.2.1 : ℂ) * mono x.2.1 (zpt n s)) *
        ∏ r, ((gq q (x.2.2.2 r) : ℂ) * mono (x.2.2.2 r) (zpt n s)) := by
  have hm0 : (expFreq n x : ℂ) ≠ 0 := by exact_mod_cast (expFreq_pos hn x).ne'
  have hsq : ((Real.sqrt (expFreq n x) : ℝ) : ℂ) = (expFreq n x : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rfl
  have hpow : (expFreq n x : ℂ) ^ (1 / 2 : ℂ) * (expFreq n x : ℂ) ^ (-s) =
      mono x.2.1 (zpt n s) * ∏ r, mono (x.2.2.2 r) (zpt n s) := by
    rw [← cpow_add _ _ hm0, show (1 / 2 : ℂ) + -s = 1 / 2 - s by ring]
    simp_rw [mono_zpt]
    rw [← natCast_prod_cpow, ← natCast_mul_natCast_cpow, expFreq, Nat.cast_mul]
  unfold expCoef
  push_cast
  rw [hsq, mul_assoc, hpow, prod_mul_distrib]
  ring

theorem norm_expTerm_eq {n : Fin k → ℕ} (hn : ∀ j, 2 ≤ n j) (q : Finset (Fin k) → ℝ)
    (x : ExpIdx k) :
    |expCoef q n x| * (expFreq n x : ℝ) ^ (-(3 / 2 : ℝ)) =
      Real.log (n x.1) * (|coefT q x.1 x.2.1| * ((Nprod n x.2.1 : ℕ) : ℝ)⁻¹) *
        ∏ r, (|gq q (x.2.2.2 r)| * ((Nprod n (x.2.2.2 r) : ℕ) : ℝ)⁻¹) := by
  have hm : (0 : ℝ) < expFreq n x := by exact_mod_cast expFreq_pos hn x
  have hlog : 0 ≤ Real.log (n x.1) := Real.log_nonneg (by exact_mod_cast
    (show 1 ≤ n x.1 by have := hn x.1; omega))
  have hsq : Real.sqrt (expFreq n x) * (expFreq n x : ℝ) ^ (-(3 / 2 : ℝ)) =
      ((expFreq n x : ℕ) : ℝ)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hm, ← Real.rpow_neg_one]
    norm_num
  have hinv : ((expFreq n x : ℕ) : ℝ)⁻¹ =
      ((Nprod n x.2.1 : ℕ) : ℝ)⁻¹ * ∏ r, ((Nprod n (x.2.2.2 r) : ℕ) : ℝ)⁻¹ := by
    unfold expFreq
    rw [Nat.cast_mul, Nat.cast_prod, mul_inv, prod_inv_distrib]
  unfold expCoef
  rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg hlog,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_prod, mul_assoc, hsq, hinv, prod_mul_distrib]
  ring

/-- The majorant `log n_j |[j ∈ T] q_T/q_∅| N_T⁻¹ Π_r |g_{p_r}| N_{p_r}⁻¹` of an expansion term at
`Re s ≥ 3/2`. -/
def expMaj (q : Finset (Fin k) → ℝ) (n : Fin k → ℕ) (x : ExpIdx k) : ℝ :=
  Real.log (n x.1) * (|coefT q x.1 x.2.1| * ((Nprod n x.2.1 : ℕ) : ℝ)⁻¹) *
    ∏ r, (|gq q (x.2.2.2 r)| * ((Nprod n (x.2.2.2 r) : ℕ) : ℝ)⁻¹)

theorem expMaj_nonneg {n : Fin k → ℕ} (hn : ∀ j, 2 ≤ n j) (q : Finset (Fin k) → ℝ)
    (x : ExpIdx k) : 0 ≤ expMaj q n x := by
  have hlog : 0 ≤ Real.log (n x.1) := Real.log_nonneg (by exact_mod_cast
    (show 1 ≤ n x.1 by have := hn x.1; omega))
  unfold expMaj
  have hp : 0 ≤ ∏ r, (|gq q (x.2.2.2 r)| * ((Nprod n (x.2.2.2 r) : ℕ) : ℝ)⁻¹) :=
    prod_nonneg fun r _ => by positivity
  positivity

theorem summable_expMaj {n : Fin k → ℕ} (hn : ∀ j, 2 ≤ n j) (q : Finset (Fin k) → ℝ)
    (hrho : ∑ S, |gq q S| * ((Nprod n S : ℕ) : ℝ)⁻¹ < 1) : Summable (expMaj q n) := by
  set ρ := ∑ S, |gq q S| * ((Nprod n S : ℕ) : ℝ)⁻¹ with hρ
  have hρ0 : 0 ≤ ρ := sum_nonneg fun S _ => by positivity
  have hpow : ∀ ℓ : ℕ, ∑ p : Fin ℓ → Finset (Fin k),
      ∏ r, (|gq q (p r)| * ((Nprod n (p r) : ℕ) : ℝ)⁻¹) = ρ ^ ℓ := fun ℓ =>
    (Fintype.sum_pow (fun S => |gq q S| * ((Nprod n S : ℕ) : ℝ)⁻¹) ℓ).symm
  have hsig : ∀ (j : Fin k) (T : Finset (Fin k)),
      Summable fun σ : (Σ ℓ : ℕ, Fin ℓ → Finset (Fin k)) => expMaj q n (j, T, σ) := by
    intro j T
    refine (summable_sigma_of_nonneg (fun σ => expMaj_nonneg hn q _)).mpr
      ⟨fun ℓ => Summable.of_finite, ?_⟩
    have hval : ∀ ℓ : ℕ, ∑' p : Fin ℓ → Finset (Fin k), expMaj q n (j, T, ⟨ℓ, p⟩) =
        Real.log (n j) * (|coefT q j T| * ((Nprod n T : ℕ) : ℝ)⁻¹) * ρ ^ ℓ := by
      intro ℓ
      rw [tsum_fintype, ← hpow ℓ, mul_sum]
      rfl
    simp_rw [hval]
    exact (summable_geometric_of_lt_one hρ0 hrho).mul_left _
  have hT : ∀ j : Fin k, Summable fun y : Finset (Fin k) × (Σ ℓ : ℕ, Fin ℓ → Finset (Fin k)) =>
      expMaj q n (j, y) := fun j =>
    (summable_prod_of_nonneg (fun y => expMaj_nonneg hn q _)).mpr
      ⟨fun T => hsig j T, Summable.of_finite⟩
  exact (summable_prod_of_nonneg (fun x => expMaj_nonneg hn q x)).mpr ⟨hT, Summable.of_finite⟩

/-- **The Dirichlet expansion of `H`.**  On `Re s ≥ 3/2`,
`H(s) − ½ Σ_j log n_j = Σ_x c_x m_x^{−s}` absolutely. -/
theorem hasSum_expTerm {q : Finset (Fin k) → ℝ} (hq0 : q ∅ ≠ 0) {n : Fin k → ℕ}
    (hn : ∀ j, 2 ≤ n j) (hrho : ∑ S, |gq q S| * ((Nprod n S : ℕ) : ℝ)⁻¹ < 1) {s : ℂ}
    (hs : 3 / 2 ≤ s.re) :
    HasSum (fun x : ExpIdx k => (expCoef q n x : ℂ) * (expFreq n x : ℂ) ^ (-s))
      (stableH q n s - ∑ j, (Real.log (n j) : ℂ) / 2) := by
  set z := zpt n s with hz
  set G : ℂ := ∑ S, (gq q S : ℂ) * mono S z with hG
  have hGn : ‖G‖ < 1 := by
    refine (norm_sum_le _ _).trans_lt (lt_of_le_of_lt (sum_le_sum fun S _ => ?_) hrho)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_mono_zpt_le hn S hs) (abs_nonneg _)
  have hQ : maQ q z = q ∅ * (1 - G) := maQ_eq_geom q hq0 z
  have hq0' : (q ∅ : ℂ) ≠ 0 := by exact_mod_cast hq0
  have h1G : (1 : ℂ) - G ≠ 0 := by
    intro h
    have : ‖G‖ = 1 := by rw [show G = 1 by linear_combination -h, norm_one]
    linarith
  set f : ExpIdx k → ℂ := fun x => (expCoef q n x : ℂ) * (expFreq n x : ℂ) ^ (-s) with hf
  have hsum : Summable f := by
    refine Summable.of_norm_bounded (summable_expMaj hn q hrho) fun x => ?_
    have hfx : (1 : ℝ) ≤ expFreq n x := by exact_mod_cast expFreq_pos hn x
    rw [hf]
    simp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_natCast_cpow_of_pos (expFreq_pos hn x), expMaj, ← norm_expTerm_eq hn q x]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hfx ?_) (abs_nonneg _)
    simp only [neg_re]
    linarith
  -- the innermost sum over `p`
  have hp : ∀ (j : Fin k) (T : Finset (Fin k)) (ℓ : ℕ),
      ∑' p : Fin ℓ → Finset (Fin k), f (j, T, ⟨ℓ, p⟩) =
        -(Real.log (n j) : ℂ) * ((coefT q j T : ℂ) * mono T z) * G ^ ℓ := by
    intro j T ℓ
    rw [tsum_fintype]
    simp only [hf]
    simp_rw [expTerm_eq hn q _ s]
    rw [← mul_sum, hG, Fintype.sum_pow]
  -- the sum over `ℓ`
  have hℓ : ∀ (j : Fin k) (T : Finset (Fin k)),
      ∑' σ : (Σ ℓ : ℕ, Fin ℓ → Finset (Fin k)), f (j, T, σ) =
        -(Real.log (n j) : ℂ) * ((coefT q j T : ℂ) * mono T z) * (1 - G)⁻¹ := by
    intro j T
    have hsl : Summable fun σ : (Σ ℓ : ℕ, Fin ℓ → Finset (Fin k)) => f (j, T, σ) :=
      (hsum.prod_factor j).prod_factor T
    rw [hsl.tsum_sigma]
    simp_rw [hp j T]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hGn]
  -- the sum over `T`
  have hTsum : ∀ j : Fin k,
      ∑' y : Finset (Fin k) × (Σ ℓ : ℕ, Fin ℓ → Finset (Fin k)), f (j, y) =
        -(Real.log (n j) : ℂ) * (maE q j z / maQ q z) := by
    intro j
    rw [(hsum.prod_factor j).tsum_prod, tsum_fintype]
    simp_rw [hℓ j]
    rw [← sum_mul, ← mul_sum, hQ]
    have hE : ∑ T, (coefT q j T : ℂ) * mono T z = maE q j z / q ∅ := by
      unfold maE coefT
      rw [sum_div, sum_filter]
      refine sum_congr rfl fun T _ => ?_
      split_ifs <;> push_cast <;> ring
    rw [hE]
    field_simp
  have htot : ∑' x, f x = stableH q n s - ∑ j, (Real.log (n j) : ℂ) / 2 := by
    rw [hsum.tsum_prod, tsum_fintype]
    simp_rw [hTsum]
    unfold stableH
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [← htot]
  exact hsum.hasSum

/-! ## The theorem -/

/-- The Dirichlet coefficients of `H`: the constant `½ Σ_j log n_j` at `1`, plus the grouped
expansion coefficients. -/
def stableCoef (q : Finset (Fin k) → ℝ) (n : Fin k → ℕ) (m : ℕ) : ℝ :=
  (if m = 1 then ∑ j, Real.log (n j) / 2 else 0) + ∑' x : expFreq n ⁻¹' {m}, expCoef q n x

theorem stableCoef_one {n : Fin k → ℕ} (hn : ∀ j, 2 ≤ n j) (q : Finset (Fin k) → ℝ) :
    stableCoef q n 1 = ∑ j, Real.log (n j) / 2 := by
  unfold stableCoef
  rw [if_pos rfl]
  have h0 : ∀ x : expFreq n ⁻¹' {1}, expCoef q n x = 0 := by
    intro x
    have hx : expFreq n x.1 = 1 := x.2
    have hT : Nprod n x.1.2.1 = 1 := Nat.eq_one_of_mul_eq_one_right hx
    have hT0 := Nprod_eq_one hn hT
    unfold expCoef coefT
    rw [hT0, if_neg (Finset.notMem_empty _)]
    simp
  rw [tsum_congr h0, tsum_zero, add_zero]

/-- `H` is the Dirichlet series of `stableCoef` on `Re s ≥ 3/2`, absolutely at `3/2`. -/
theorem stableH_eq_LSeries {q : Finset (Fin k) → ℝ} (hq0 : q ∅ ≠ 0) {n : Fin k → ℕ}
    (hn : ∀ j, 2 ≤ n j) (hrho : ∑ S, |gq q S| * ((Nprod n S : ℕ) : ℝ)⁻¹ < 1) :
    LSeriesSummable (fun m => (stableCoef q n m : ℂ)) (3 / 2) ∧
      ∀ s : ℂ, 3 / 2 ≤ s.re → stableH q n s = LSeries (fun m => (stableCoef q n m : ℂ)) s := by
  set c₀ : ℝ := ∑ j, Real.log (n j) / 2 with hc₀
  have hfam : Summable fun x : ExpIdx k =>
      |expCoef q n x| * (expFreq n x : ℝ) ^ (-(3 / 2 : ℝ)) := by
    refine (summable_expMaj hn q hrho).congr fun x => ?_
    rw [norm_expTerm_eq hn q x]
    rfl
  have hg := LSeriesSummable_of_family hfam
  set g : ℕ → ℂ := fun m => ((∑' x : expFreq n ⁻¹' {m}, expCoef q n x : ℝ) : ℂ) with hgdef
  set d : ℕ → ℂ := fun m => if m = 1 then (c₀ : ℂ) else 0 with hd
  have hdsum : ∀ s : ℂ, LSeriesSummable d s := fun s =>
    summable_of_ne_finset_zero (s := {1}) fun m hm => by
      rw [Finset.mem_singleton] at hm
      simp [LSeries.term, hd, hm]
  have hdval : ∀ s : ℂ, LSeries d s = c₀ := by
    intro s
    rw [LSeries, tsum_eq_single 1]
    · simp [LSeries.term, hd]
    · intro m hm
      simp [LSeries.term, hd, hm]
  have hcoef : (fun m => (stableCoef q n m : ℂ)) = d + g := by
    funext m
    simp only [Pi.add_apply, hd, hgdef, stableCoef]
    push_cast
    split_ifs <;> simp [hc₀]
  have h32 : ((3 / 2 : ℝ) : ℂ) = 3 / 2 := by push_cast; ring
  have hg' : LSeriesSummable g (3 / 2) := by rw [← h32]; exact hg
  refine ⟨?_, fun s hs => ?_⟩
  · rw [hcoef]
    exact (hdsum _).add hg'
  · have hgs : LSeriesSummable g s :=
      hg'.of_re_le_re (by simpa using hs)
    rw [hcoef, LSeries_add (hdsum s) hgs, hdval]
    have h1 := hasSum_LSeries_of_family (fun x => expFreq_pos hn x) hfam
      (s := s) (by simpa using hs)
    have h2 := hasSum_expTerm hq0 hn hrho hs
    have heq := h1.unique h2
    rw [hgdef, heq, hc₀]
    push_cast
    ring

/-- **Stable Dirichlet polynomials have critical zeros off the zeros of `ζ`.**  Let `k ≥ 1`,
`n_j ≥ 2`, and let `Q(z) = Σ_S q_S z^S` be real multiaffine, stable on the open unit polydisc,
self-reciprocal (`q_{Sᶜ} = q_S`), with `q_∅ ≠ 0` and `Σ_{S ≠ ∅} |q_S/q_∅| Π_{j∈S} n_j^{−1} < 1`.
Then `P(s) = Q(n₁^{½−s}, …, n_k^{½−s})` has a zero `½ + it` with `ζ(½ + it) ≠ 0`. -/
theorem exists_zero_stableDirichlet_riemannZeta_ne_zero (hk : 0 < k) {q : Finset (Fin k) → ℝ}
    {n : Fin k → ℕ} (hn : ∀ j, 2 ≤ n j) (hst : Stable q) (hq : SelfRecip q) (hq0 : q ∅ ≠ 0)
    (hsmall : ∑ S ∈ univ.erase ∅, |q S / q ∅| * ((Nprod n S : ℕ) : ℝ)⁻¹ < 1) :
    ∃ t : ℝ, maQ q (zpt n ((1 / 2 : ℂ) + t * I)) = 0 ∧
      riemannZeta ((1 / 2 : ℂ) + t * I) ≠ 0 := by
  have hrho : ∑ S, |gq q S| * ((Nprod n S : ℕ) : ℝ)⁻¹ < 1 := by
    have heq : ∑ S, |gq q S| * ((Nprod n S : ℕ) : ℝ)⁻¹ =
        ∑ S ∈ univ.erase ∅, |q S / q ∅| * ((Nprod n S : ℕ) : ℝ)⁻¹ := by
      rw [← add_sum_erase _ _ (mem_univ ∅)]
      have h0 : |gq q ∅| * ((Nprod n ∅ : ℕ) : ℝ)⁻¹ = 0 := by simp [gq]
      rw [h0, zero_add]
      refine sum_congr rfl fun S hS => ?_
      simp [gq, ne_of_mem_erase hS, abs_neg]
    rw [heq]
    exact hsmall
  by_contra hcon
  push Not at hcon
  obtain ⟨hAs, hA⟩ := stableH_eq_LSeries hq0 hn hrho
  have h := AtomDomination.eq_zero_of_herglotz_dirichlet_criticalCarrier
    (differentiableOn_stableH hst hn) (fun s hs => re_stableH_nonneg hst hn hs) hAs hA
    (fun t ht => tendsto_re_stableH_critical hq hn fun hP => ht (hcon t hP)) 1 le_rfl
  rw [stableCoef_one hn q] at h
  have hpos : 0 < ∑ j, Real.log (n j) / 2 := by
    have hne : (univ : Finset (Fin k)).Nonempty := univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩
    refine sum_pos (fun j _ => ?_) hne
    have : (1 : ℝ) < n j := by exact_mod_cast (show 1 < n j by have := hn j; omega)
    have := Real.log_pos this
    positivity
  linarith

/-! ## A two-prime Lee–Yang family -/

/-- `Q_a(z₁, z₂) = 1 + a(z₁ + z₂) + z₁z₂`. -/
def leeYangQ (a : ℝ) (S : Finset (Fin 2)) : ℝ := if S.card = 1 then a else 1

theorem maQ_leeYang (a : ℝ) (z : Fin 2 → ℂ) :
    maQ (leeYangQ a) z = 1 + a * (z 0 + z 1) + z 0 * z 1 := by
  unfold maQ
  rw [show (univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
  have h0 : leeYangQ a ∅ = 1 := by simp [leeYangQ]
  have h1 : leeYangQ a {0} = a := by simp [leeYangQ]
  have h2 : leeYangQ a {1} = a := by simp [leeYangQ]
  have h3 : leeYangQ a {0, 1} = 1 := by
    unfold leeYangQ
    rw [if_neg (by decide)]
  rw [h0, h1, h2, h3]
  simp [mono]
  ring

theorem selfRecip_leeYang (a : ℝ) : SelfRecip (leeYangQ a) := by
  intro S
  unfold leeYangQ
  have h : (Sᶜ).card = 1 ↔ S.card = 1 := by
    revert S
    decide
  simp only [h]

theorem stable_leeYang {a : ℝ} (ha : |a| < 1) : Stable (leeYangQ a) := by
  intro z hz h
  rw [maQ_leeYang] at h
  set u := z 0 with hu
  set v := z 1 with hv
  have hu1 := hz 0
  have hv1 := hz 1
  have ha2 : a ^ 2 < 1 := by nlinarith [abs_nonneg a, sq_abs a]
  have hu2 : u.re ^ 2 + u.im ^ 2 < 1 := by
    have h1 := Complex.sq_norm u
    rw [normSq_apply] at h1
    nlinarith [norm_nonneg u]
  have key : ‖(a : ℂ) + u‖ < ‖1 + (a : ℂ) * u‖ := by
    rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      normSq_apply, normSq_apply]
    simp only [add_re, ofReal_re, add_im, ofReal_im, one_re, one_im, mul_re, mul_im,
      zero_add, zero_mul, sub_zero]
    nlinarith [mul_pos (sub_pos.mpr ha2) (sub_pos.mpr hu2)]
  have h2 : (1 : ℂ) + a * u = -(v * (a + u)) := by linear_combination h
  rw [h2, norm_neg, norm_mul] at key
  have := mul_le_of_le_one_left (norm_nonneg ((a : ℂ) + u)) hv1.le
  linarith

/-- **The two-prime Lee–Yang family.**  For every real `|a| < 1` some zero of
`1 + a(2^{−it} + 3^{−it}) + 6^{−it}` is not the ordinate of a zero of `ζ`. -/
theorem exists_zero_leeYang_riemannZeta_ne_zero {a : ℝ} (ha : |a| < 1) :
    ∃ t : ℝ, 1 + a * ((2 : ℂ) ^ (-(t * I)) + (3 : ℂ) ^ (-(t * I))) + (6 : ℂ) ^ (-(t * I)) = 0 ∧
      riemannZeta ((1 / 2 : ℂ) + t * I) ≠ 0 := by
  have hn : ∀ j, 2 ≤ (![2, 3] : Fin 2 → ℕ) j := by decide
  have hsmall : ∑ S ∈ univ.erase ∅, |leeYangQ a S / leeYangQ a ∅| *
      ((Nprod ![2, 3] S : ℕ) : ℝ)⁻¹ < 1 := by
    rw [show (univ : Finset (Finset (Fin 2))).erase ∅ = {{0}, {1}, {0, 1}} by decide,
      sum_insert (by decide), sum_insert (by decide), sum_singleton]
    have h0 : leeYangQ a ∅ = 1 := by simp [leeYangQ]
    have h1 : leeYangQ a {0} = a := by simp [leeYangQ]
    have h2 : leeYangQ a {1} = a := by simp [leeYangQ]
    have h3 : leeYangQ a {0, 1} = 1 := by
      unfold leeYangQ
      rw [if_neg (by decide)]
    have n0 : Nprod ![2, 3] {0} = 2 := by decide
    have n1 : Nprod ![2, 3] {1} = 3 := by decide
    have n2 : Nprod ![2, 3] {0, 1} = 6 := by decide
    rw [h0, h1, h2, h3, n0, n1, n2]
    norm_num
    linarith
  obtain ⟨t, hP, hz⟩ := exists_zero_stableDirichlet_riemannZeta_ne_zero (by norm_num) hn
    (stable_leeYang ha) (selfRecip_leeYang a) (by simp [leeYangQ]) hsmall
  refine ⟨t, ?_, hz⟩
  rw [maQ_leeYang] at hP
  have e : ∀ m : ℕ, (m : ℂ) ^ ((1 / 2 : ℂ) - ((1 / 2 : ℂ) + t * I)) = (m : ℂ) ^ (-(t * I)) :=
    fun m => by ring_nf
  have z0 : zpt ![2, 3] ((1 / 2 : ℂ) + t * I) 0 = (2 : ℂ) ^ (-(t * I)) := by
    unfold zpt
    rw [e]
    simp
  have z1 : zpt ![2, 3] ((1 / 2 : ℂ) + t * I) 1 = (3 : ℂ) ^ (-(t * I)) := by
    unfold zpt
    rw [e]
    simp
  have h6 : (2 : ℂ) ^ (-(t * I)) * (3 : ℂ) ^ (-(t * I)) = (6 : ℂ) ^ (-(t * I)) := by
    have := natCast_mul_natCast_cpow 2 3 (-(t * I))
    push_cast at this
    rw [← this]
    norm_num
  rw [z0, z1, h6] at hP
  exact hP

end RHTower.StablePutnam
