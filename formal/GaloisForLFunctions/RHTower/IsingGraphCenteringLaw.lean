import GaloisForLFunctions.RHTower.LeeYangIsingGraphDatum
import GaloisForLFunctions.RHTower.FiniteDirichletCriticalNonannihilation
import GaloisForLFunctions.RHTower.XiCentralDiscBound

/-!
# The centering law for ferromagnetic Ising producers of `Ξ`

Let `Z(z) = Σ_S c_S e^{−iΛ_S z}` be the partition function of a finite Ising graph with nonnegative
bond weights `c_S ≥ 0`, nonnegative field frequencies `λ_k`, and total field `Λ = Σ_k λ_k`.
Here `Λ_S = Σ_{k∈S} λ_k`.

* `sum_exp_eq_exp_mul`: spin-flip symmetry gives `Z(iy) = e^{Λy} Z(−iy)` on the imaginary axis.
* `norm_exp_mul_isingPart_le`: `‖e^{iβz} Z(z)‖ ≤ Z(0) e^{(Λ+|β|)‖z‖}`.
* `not_exponentialType_mul_XiC`: `E·Ξ` is not of exponential type, for any entire zero-free `E`.
  It vanishes at the superlinearly many simple critical ordinates.

**Centering law** (`isingGraph_centering_law`). Suppose `κ_n e^{iβ_n z} Z_n(z) → E(z)Ξ(z)` locally
uniformly, with constants `κ_n`, real phases `β_n`, and `E` entire and zero-free. Then
`Λ_n → ∞` and `Λ_n − 2β_n` converges. The proof uses neither the Lee–Yang theorem nor any bound on
the couplings.

**Consequences.**
* `not_tendstoLocallyUniformly_isingGraph_const_mul_XiC`: no constant normalization works. For
  nonnegative bonds, the constant-normalized capstone
  `riemannHypothesis_of_isingGraph_tendstoLocallyUniformly_mul_XiC` has an unsatisfiable hypothesis.
  The same holds for the constant-normalized field-density budget applied to Ising data.
* `riemannHypothesis_of_isingGraph_phase_tendstoLocallyUniformly_mul_XiC`: the phase-normalized
  capstone. By the centering law its normalizer must be asymptotically `e^{iΛ_n z/2}`, the
  characteristic function of the centered magnetization, with total field `Λ_n → ∞`.
-/

open Complex Filter Topology Finset
open GaloisForLFunctions.HTGeometry.LeeYang

namespace RHTower.LeeYangCount

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The total field frequency of a set of sites. -/
def fieldSum (freq : V → ℝ) (S : Finset V) : ℝ := ∑ k ∈ S, freq k

/-- The Ising coefficients as real numbers. -/
def isingCoeffR (a : V → V → ℝ) (E : Finset (V × V)) (S : Finset V) : ℝ :=
  ∏ p ∈ E, if (p.1 ∈ S ↔ p.2 ∈ S) then 1 else a p.1 p.2

omit [Fintype V] in
theorem isingCoeff_eq_ofReal (a : V → V → ℝ) (E : Finset (V × V)) (S : Finset V) :
    isingCoeff a E S = (isingCoeffR a E S : ℂ) := by
  rw [isingCoeff, isingCoeffR, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  simp only [bondWeight]
  split_ifs <;> simp

omit [Fintype V] in
theorem isingCoeffR_nonneg {a : V → V → ℝ} {E : Finset (V × V)} (ha : ∀ p ∈ E, 0 ≤ a p.1 p.2)
    (S : Finset V) : 0 ≤ isingCoeffR a E S :=
  Finset.prod_nonneg fun p hp => by
    split_ifs
    · norm_num
    · exact ha p hp

theorem isingCoeffR_compl (a : V → V → ℝ) (E : Finset (V × V)) (S : Finset V) :
    isingCoeffR a E Sᶜ = isingCoeffR a E S := by
  have h := isingCoeff_compl a E S
  rw [isingCoeff_eq_ofReal, isingCoeff_eq_ofReal] at h
  exact_mod_cast h

omit [Fintype V] in
theorem isingCoeffR_empty (a : V → V → ℝ) (E : Finset (V × V)) : isingCoeffR a E ∅ = 1 := by
  simp [isingCoeffR]

theorem fieldSum_compl (freq : V → ℝ) (S : Finset V) :
    fieldSum freq Sᶜ = fieldSum freq univ - fieldSum freq S := by
  rw [fieldSum, fieldSum, fieldSum, ← Finset.sum_compl_add_sum S freq]
  ring

omit [Fintype V] [DecidableEq V] in
theorem fieldSum_nonneg {freq : V → ℝ} (hfreq : ∀ k, 0 ≤ freq k) (S : Finset V) :
    0 ≤ fieldSum freq S :=
  Finset.sum_nonneg fun k _ => hfreq k

omit [DecidableEq V] in
theorem fieldSum_le {freq : V → ℝ} (hfreq : ∀ k, 0 ≤ freq k) (S : Finset V) :
    fieldSum freq S ≤ fieldSum freq univ :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun k _ _ => hfreq k

/-- The Ising partition function with fields `e^{−iλ_k z}`. -/
def isingPart (a : V → V → ℝ) (E : Finset (V × V)) (freq : V → ℝ) (z : ℂ) : ℂ :=
  maEval (isingCoeff a E) (fun k => Complex.exp (-(I * (freq k : ℂ) * z)))

theorem isingPart_eq_sum (a : V → V → ℝ) (E : Finset (V × V)) (freq : V → ℝ) (z : ℂ) :
    isingPart a E freq z =
      ∑ S : Finset V, (isingCoeffR a E S : ℂ) * Complex.exp (-(I * (fieldSum freq S : ℂ) * z)) := by
  rw [isingPart, maEval]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [isingCoeff_eq_ofReal, ← Complex.exp_sum]
  congr 2
  simp only [fieldSum, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_neg_distrib]

/-- On the imaginary axis the partition function is the positive sum `Σ_S c_S e^{Λ_S y}`. -/
theorem isingPart_mul_I (a : V → V → ℝ) (E : Finset (V × V)) (freq : V → ℝ) (y : ℝ) :
    isingPart a E freq ((y : ℂ) * I) =
      ((∑ S : Finset V, isingCoeffR a E S * Real.exp (fieldSum freq S * y) : ℝ) : ℂ) := by
  rw [isingPart_eq_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  have hI : I * I = -1 := Complex.I_mul_I
  push_cast
  linear_combination (-(↑(fieldSum freq S) * ↑y) : ℂ) * hI

/-- **Spin-flip symmetry on the imaginary axis.** `Z(iy) = e^{Λy} Z(−iy)`. -/
theorem sum_exp_eq_exp_mul (a : V → V → ℝ) (E : Finset (V × V)) (freq : V → ℝ) (y : ℝ) :
    ∑ S : Finset V, isingCoeffR a E S * Real.exp (fieldSum freq S * y) =
      Real.exp (fieldSum freq univ * y) *
        ∑ S : Finset V, isingCoeffR a E S * Real.exp (fieldSum freq S * -y) := by
  rw [Finset.mul_sum]
  refine Fintype.sum_bijective compl compl_involutive.bijective _ _ fun S => ?_
  rw [isingCoeffR_compl, fieldSum_compl, ← mul_assoc, mul_comm (Real.exp _), mul_assoc,
    ← Real.exp_add]
  congr 2
  ring

/-- **Exponential-type bound.** With nonnegative bonds and fields, `‖e^{iβz} Z(z)‖ ≤ Z(0)
e^{(Λ+|β|)‖z‖}`. -/
theorem norm_exp_mul_isingPart_le {a : V → V → ℝ} {E : Finset (V × V)}
    (ha : ∀ p ∈ E, 0 ≤ a p.1 p.2) {freq : V → ℝ} (hfreq : ∀ k, 0 ≤ freq k) (β : ℝ) (z : ℂ) :
    ‖Complex.exp (I * (β : ℂ) * z) * isingPart a E freq z‖ ≤
      (∑ S : Finset V, isingCoeffR a E S) *
        Real.exp ((fieldSum freq univ + |β|) * ‖z‖) := by
  rw [isingPart_eq_sum, Finset.mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun S _ => ?_)
  rw [← mul_assoc, mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (isingCoeffR_nonneg ha S), Complex.norm_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (isingCoeffR_nonneg ha S)
  have hre : (I * (β : ℂ) * z + -(I * (fieldSum freq S : ℂ) * z)).re =
      (fieldSum freq S - β) * z.im := by
    simp [Complex.mul_re, Complex.mul_im]
    ring
  rw [hre]
  have h0 := fieldSum_nonneg hfreq S
  have h1 := fieldSum_le hfreq S
  have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  calc (fieldSum freq S - β) * z.im ≤ |fieldSum freq S - β| * |z.im| := by
        rw [← abs_mul]; exact le_abs_self _
    _ ≤ (fieldSum freq univ + |β|) * ‖z‖ := by
        refine mul_le_mul ?_ him (abs_nonneg _)
          (add_nonneg (fieldSum_nonneg hfreq univ) (abs_nonneg β))
        refine (abs_sub _ _).trans ?_
        rw [abs_of_nonneg h0]
        linarith

/-- `E·Ξ` is never of exponential type: a nonzero function of exponential type is nonzero at some
simple critical ordinate, while `E·Ξ` vanishes at all of them. -/
theorem not_exponentialType_mul_XiC {Ef : ℂ → ℂ} (hEf : Differentiable ℂ Ef)
    (hEf0 : ∀ z, Ef z ≠ 0) {A C : ℝ} (hA : 0 ≤ A) (hC : 1 ≤ C) :
    ¬ ∀ z : ℂ, ‖Ef z * XiC z‖ ≤ C * Real.exp (A * ‖z‖) := by
  intro hgrow
  have hXiCd : Differentiable ℂ XiC := fun z => (XiC_analytic z (Set.mem_univ z)).differentiableAt
  have hFne : (fun z => Ef z * XiC z) ≠ 0 := fun h =>
    mul_ne_zero (hEf0 0) XiC_zero_ne (congrFun h 0)
  obtain ⟨t, -, -, hxi, -, hne⟩ :=
    exists_simpleCritical_nonzero_of_exponentialType (hEf.mul hXiCd) hFne hA hC hgrow ∅
  apply hne
  have hXi : XiC (t : ℂ) = xi (linePt t) := by
    simp only [XiC, linePt]
    push_cast
    ring_nf
  show Ef (t : ℂ) * XiC (t : ℂ) = 0
  rw [hXi, hxi, mul_zero]

/-- The phase-normalized partition function at `±i`: `f(i) = e^{Λ−2β} f(−i)`. -/
theorem phase_isingPart_I (a : V → V → ℝ) (E : Finset (V × V)) (freq : V → ℝ) (κ : ℂ) (β : ℝ) :
    κ * (Complex.exp (I * (β : ℂ) * I) * isingPart a E freq I) =
      (Real.exp (fieldSum freq univ - 2 * β) : ℂ) *
        (κ * (Complex.exp (I * (β : ℂ) * -I) * isingPart a E freq (-I))) := by
  have h1 := isingPart_mul_I a E freq 1
  have h2 := isingPart_mul_I a E freq (-1)
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_neg, neg_mul] at h1 h2
  rw [h1, h2, sum_exp_eq_exp_mul a E freq 1]
  set s : ℝ := ∑ S : Finset V, isingCoeffR a E S * Real.exp (fieldSum freq S * -1)
  have e1 : Complex.exp (I * (β : ℂ) * I) = (Real.exp (-β) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    linear_combination (β : ℂ) * Complex.I_mul_I
  have e2 : Complex.exp (I * (β : ℂ) * -I) = (Real.exp β : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    linear_combination (-(β : ℂ)) * Complex.I_mul_I
  have hreal : Real.exp (-β) * Real.exp (fieldSum freq univ * 1) =
      Real.exp (fieldSum freq univ - 2 * β) * Real.exp β := by
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  have hc : (Real.exp (-β) : ℂ) * (Real.exp (fieldSum freq univ * 1) : ℂ) =
      (Real.exp (fieldSum freq univ - 2 * β) : ℂ) * (Real.exp β : ℂ) := by
    exact_mod_cast hreal
  rw [e1, e2, Complex.ofReal_mul]
  linear_combination κ * (s : ℂ) * hc

/-- **Centering law for ferromagnetic Ising producers of `Ξ`.** Take finite Ising graphs with
nonnegative bond weights and nonnegative field frequencies, constants `κ_n` and phases `β_n`. If
`κ_n e^{iβ_n z} Z_n(z) → E(z)Ξ(z)` locally uniformly (`E` entire and zero-free), then the total
field `Λ_n = Σ_k λ_{n,k}` tends to infinity while `Λ_n − 2β_n` converges. The normalizing phase is
asymptotically the centering `e^{iΛ_n z/2}`.

The proof needs neither the Lee–Yang theorem nor any coupling bound. Spin-flip symmetry gives
`f_n(i) = e^{Λ_n − 2β_n} f_n(−i)`, so `Λ_n − 2β_n` converges. Nonnegative coefficients give
`‖f_n(z)‖ ≤ ‖f_n(0)‖ e^{(Λ_n + |β_n|)‖z‖}`. A bounded subsequence of `Λ_n` would make the limit of
exponential type, but `E·Ξ` vanishes at superlinearly many simple critical ordinates. -/
theorem isingGraph_centering_law
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (a : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (ha : ∀ n, ∀ q ∈ E n, 0 ≤ a n q.1 q.2)
    (freq : ∀ n, ι n → ℝ) (hfreq : ∀ n j, 0 ≤ freq n j) (κ : ℕ → ℂ) (β : ℕ → ℝ)
    {Ef : ℂ → ℂ} (hEf : Differentiable ℂ Ef) (hEf0 : ∀ z, Ef z ≠ 0)
    (hconv : TendstoLocallyUniformly
      (fun n z => κ n * (Complex.exp (I * (β n : ℂ) * z) * isingPart (a n) (E n) (freq n) z))
      (fun z => Ef z * XiC z) atTop) :
    Tendsto (fun n => fieldSum (freq n) univ) atTop atTop ∧
      ∃ L : ℝ, Tendsto (fun n => fieldSum (freq n) univ - 2 * β n) atTop (𝓝 L) := by
  set f : ℕ → ℂ → ℂ := fun n z =>
    κ n * (Complex.exp (I * (β n : ℂ) * z) * isingPart (a n) (E n) (freq n) z) with hf
  set F : ℂ → ℂ := fun z => Ef z * XiC z with hF
  have hXiCd : Differentiable ℂ XiC := fun z => (XiC_analytic z (Set.mem_univ z)).differentiableAt
  have hFd : Differentiable ℂ F := hEf.mul hXiCd
  have hpt : ∀ w, Tendsto (fun n => f n w) atTop (𝓝 (F w)) := fun w =>
    hconv.tendsto_comp hFd.continuous.continuousAt tendsto_const_nhds
  have hFw : ∀ w : ℂ, ‖w‖ ≤ 1 → F w ≠ 0 := fun w hw =>
    mul_ne_zero (hEf0 w) (XiC_ne_zero_of_norm_le_one hw)
  have hFI : F I ≠ 0 := hFw I (by simp)
  have hFmI : F (-I) ≠ 0 := hFw (-I) (by simp)
  set Λ : ℕ → ℝ := fun n => fieldSum (freq n) univ with hΛ
  -- the exponential converges
  have hexp : Tendsto (fun n => (Real.exp (Λ n - 2 * β n) : ℂ)) atTop (𝓝 (F I / F (-I))) := by
    refine ((hpt I).div (hpt (-I)) hFmI).congr' ?_
    filter_upwards [(hpt (-I)).eventually_ne hFmI] with n hn
    show f n I / f n (-I) = _
    simp only [hf] at hn ⊢
    rw [phase_isingPart_I, mul_div_assoc, div_self hn, mul_one]
  set L' : ℂ := F I / F (-I) with hL'
  have hre : Tendsto (fun n => Real.exp (Λ n - 2 * β n)) atTop (𝓝 L'.re) :=
    ((Complex.continuous_re.tendsto L').comp hexp).congr fun n => Complex.ofReal_re _
  have him : L'.im = 0 := by
    have h : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 L'.im) :=
      ((Complex.continuous_im.tendsto L').comp hexp).congr fun n => Complex.ofReal_im _
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  have hL'ne : L' ≠ 0 := div_ne_zero hFI hFmI
  have hpos : 0 < L'.re := by
    have hnn : 0 ≤ L'.re := ge_of_tendsto' hre fun n => (Real.exp_pos _).le
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exact absurd (Complex.ext h.symm him) hL'ne
  have hlogL : Tendsto (fun n => Λ n - 2 * β n) atTop (𝓝 (Real.log L'.re)) := by
    have h := (Real.continuousAt_log hpos.ne').tendsto.comp hre
    simpa only [Function.comp_def, Real.log_exp] using h
  refine ⟨?_, Real.log L'.re, hlogL⟩
  -- the total field diverges
  rw [tendsto_atTop]
  intro b
  by_contra hb
  rw [Filter.not_eventually] at hb
  set L : ℝ := Real.log L'.re with hLdef
  have hnear : ∀ᶠ n in atTop, |Λ n - 2 * β n - L| ≤ 1 := by
    filter_upwards [Metric.tendsto_nhds.mp hlogL 1 one_pos] with n hn
    rw [Real.dist_eq] at hn
    exact hn.le
  set A : ℝ := |b| + (|b| + |L| + 1) / 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hbound : ∃ᶠ n in atTop, ∀ z, ‖f n z‖ ≤ ‖f n 0‖ * Real.exp (A * ‖z‖) := by
    refine (hb.and_eventually hnear).mono fun n hn z => ?_
    obtain ⟨hbn, hn⟩ := hn
    have hΛ0 : 0 ≤ Λ n := fieldSum_nonneg (hfreq n) univ
    have hΛb : Λ n < b := lt_of_not_ge hbn
    have hβ : |β n| ≤ (|b| + |L| + 1) / 2 := by
      rw [abs_le] at hn ⊢
      constructor <;> linarith [le_abs_self b, neg_abs_le b, le_abs_self L, neg_abs_le L]
    have hexpo : Λ n + |β n| ≤ A := by
      rw [hA]
      linarith [le_abs_self b]
    have hsum0 : 0 ≤ ∑ S : Finset (ι n), isingCoeffR (a n) (E n) S :=
      Finset.sum_nonneg fun S _ => isingCoeffR_nonneg (ha n) S
    have h0 : f n 0 = κ n * ((∑ S : Finset (ι n), isingCoeffR (a n) (E n) S : ℝ) : ℂ) := by
      simp only [hf, mul_zero, Complex.exp_zero, one_mul, isingPart_eq_sum, neg_zero,
        Complex.ofReal_sum, mul_one]
    have hn0 : ‖f n 0‖ = ‖κ n‖ * ∑ S : Finset (ι n), isingCoeffR (a n) (E n) S := by
      rw [h0, norm_mul, Complex.norm_real, Real.norm_of_nonneg hsum0]
    rw [hn0]
    simp only [hf]
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_left ((norm_exp_mul_isingPart_le (ha n) (hfreq n) (β n) z).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hexpo (norm_nonneg z))) hsum0)) (norm_nonneg (κ n))).trans_eq
      (mul_assoc _ _ _).symm
  -- the limit is of exponential type
  have hgrow : ∀ z, ‖F z‖ ≤ ‖F 0‖ * Real.exp (A * ‖z‖) := by
    intro z
    have hclosed : IsClosed {p : ℝ × ℝ | p.1 ≤ p.2} := isClosed_le continuous_fst continuous_snd
    have hlim : Tendsto (fun n => (‖f n z‖, ‖f n 0‖ * Real.exp (A * ‖z‖))) atTop
        (𝓝 (‖F z‖, ‖F 0‖ * Real.exp (A * ‖z‖))) :=
      ((hpt z).norm).prodMk_nhds (((hpt 0).norm).mul_const _)
    exact hclosed.mem_of_frequently_of_tendsto (hbound.mono fun n hn => hn z) hlim
  exact not_exponentialType_mul_XiC hEf hEf0 hA0 (le_max_left 1 ‖F 0‖) fun z =>
    (hgrow z).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

/-- **No constant normalization.** For ferromagnetic Ising graphs (nonnegative bond weights and
fields, any topology and size), no constants `κ_n` make `κ_n Z_n` converge locally uniformly to
`E·Ξ` with `E` entire and zero-free. -/
theorem not_tendstoLocallyUniformly_isingGraph_const_mul_XiC
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (a : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (ha : ∀ n, ∀ q ∈ E n, 0 ≤ a n q.1 q.2)
    (freq : ∀ n, ι n → ℝ) (hfreq : ∀ n j, 0 ≤ freq n j) (κ : ℕ → ℂ)
    {Ef : ℂ → ℂ} (hEf : Differentiable ℂ Ef) (hEf0 : ∀ z, Ef z ≠ 0) :
    ¬ TendstoLocallyUniformly (fun n z => κ n * isingPart (a n) (E n) (freq n) z)
      (fun z => Ef z * XiC z) atTop := by
  intro hconv
  obtain ⟨hinf, L, hL⟩ := isingGraph_centering_law a E ha freq hfreq κ (fun _ => 0) hEf hEf0
    (by simpa using hconv)
  simp only [mul_zero, sub_zero] at hL
  exact not_tendsto_atTop_of_tendsto_nhds hL hinf

/-- **Phase-normalized Ising capstone.** If `κ_n e^{iβ_n z} Z_n(z) → E(z)Ξ(z)` locally uniformly for
ferromagnetic Ising graphs (`|a| ≤ 1`, bonds between distinct sites, positive fields), with `κ_n ≠ 0`
and `E` entire and zero-free, then the Riemann hypothesis holds. By `isingGraph_centering_law` this
forces `Λ_n → ∞` and `β_n = Λ_n/2 + O(1)` for nonnegative bonds. -/
theorem riemannHypothesis_of_isingGraph_phase_tendstoLocallyUniformly_mul_XiC
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (a : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (hE : ∀ n, ∀ q ∈ E n, q.1 ≠ q.2) (ha : ∀ n, ∀ q ∈ E n, |a n q.1 q.2| ≤ 1)
    (freq : ∀ n, ι n → ℝ) (hfreq : ∀ n j, 0 < freq n j) (κ : ℕ → ℂ) (hκ : ∀ n, κ n ≠ 0)
    (β : ℕ → ℝ) {Ef : ℂ → ℂ} (hEf : AnalyticOnNhd ℂ Ef Set.univ) (hEf0 : ∀ z, Ef z ≠ 0)
    (hconv : TendstoLocallyUniformly
      (fun n z => κ n * (Complex.exp (I * (β n : ℂ) * z) * isingPart (a n) (E n) (freq n) z))
      (fun z => Ef z * XiC z) atTop) :
    RiemannHypothesis := by
  set L : ∀ n, LeeYangDatum (ι n) := fun n => isingDatum (a n) (E n) (hE n) (ha n) (freq n) (hfreq n)
  have hrestr : ∀ n z, isingPart (a n) (E n) (freq n) z = (L n).restr z := by
    intro n z
    simp only [L, isingPart, LeeYangDatum.restr, LeeYangDatum.field, isingDatum, eval_isingMvPoly]
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  let z : ℂ := (ρ - 1 / 2) * (-I)
  have hXiC : XiC z = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z * I = ρ := by
      dsimp only [z]
      rw [mul_assoc]
      have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
      rw [hI, mul_one]
      ring
    rw [harg, hzero]
  have hdiff : ∀ n, Differentiable ℂ fun w =>
      κ n * (Complex.exp (I * (β n : ℂ) * w) * isingPart (a n) (E n) (freq n) w) := by
    intro n
    have h : isingPart (a n) (E n) (freq n) = (L n).restr := funext (hrestr n)
    refine (Differentiable.const_mul ?_ _)
    refine Differentiable.mul ?_ ?_
    · exact (differentiable_const _ |>.mul differentiable_id).cexp
    · rw [h]; exact (L n).differentiable_restr
  have him : z.im = 0 := zero_mem_closed_of_tendstoLocallyUniformly hconv
    (hEf.mul XiC_analytic) (Filter.Eventually.of_forall hdiff)
    (isClosed_eq Complex.continuous_im continuous_const)
    (Filter.Eventually.of_forall fun n w hw => by
      rw [hrestr] at hw
      exact (L n).restr_im_eq_zero_of_eq_zero
        ((mul_eq_zero.mp ((mul_eq_zero.mp hw).resolve_left (hκ n))).resolve_left
          (Complex.exp_ne_zero _)))
    (mul_ne_zero (hEf0 0) XiC_zero_ne) (by simp [hXiC])
  have hzIm : z.im = 1 / 2 - ρ.re := by simp [z]
  exact (ne_of_gt (mem_rightHalf.mp hρ)) (by linarith)

end

end RHTower.LeeYangCount
