import Mathlib

/-!
# Cross-system blindness of multiplicative regularization

A *Beurling system* is a sequence of generalized primes `1 < p₁ ≤ p₂ ≤ ⋯ → ∞`; it is
*Mertens-normal* when its weighted prime-power count satisfies `S(N) = log N + C + o(1)`.  The
prime log-jet Gram of the system at aperture `N` has entries `H_k(N) = ∑_{n ≤ N} Λ(n) n⁻¹ (log n)^k`,
and a *multiplicative regularization* rescales the entries, `H_k ↦ c_k^{(N)} H_k(N)`.

Three statements are proved.

* **Cross-system blindness.**  If two aperture families have the same nonzero normalized limit
  against a common divergent scale, then any regularization convergent on one converges on the
  other, to the same value.  The normalizer is not assumed to compensate; the compensation is
  extracted from the first family and then forced on the second.

* **Systems with different zero sets are identified.**  Replacing the generator `2` of the rational
  primes by `3` gives a Beurling system whose zeta function is
  `ζ(s)(1 − 2^{-s})/(1 − 3^{-s})` on the half-plane of convergence.  At `s₀ = 2πi/log 2` the factor
  `1 − 2^{-s}` vanishes, `1 − 3^{-s}` does not (because `log 3/log 2` is not an integer), and
  `ζ(s₀) ≠ 0` by the functional equation, since `1 − s₀` has real part `1`.  So `s₀` is a zero of
  the swapped system's zeta function and not of `ζ`.

* **Mertens-normality survives the swap.**  The two generator corrections are truncated geometric
  series, so each converges; the swap shifts the Mertens constant by `log 3/2 − log 2` and nothing
  else.

Together: the regularized limits cannot see the zero set, since they agree across a pair of systems
whose zero sets differ.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry.Beurling

/-! ## Cross-system blindness of a convergent regularization -/

/-- **The compensation is forced.**  If `c · H` converges and `H/L` converges to a nonzero limit,
then the normalizer's compensation `c · L` converges, to the quotient of the two limits. -/
theorem tendsto_normalizer_of_tendsto_ratio {A ℓ : ℝ} (hA : A ≠ 0) (H c L : ℝ → ℝ)
    (hH : Tendsto (fun N => H N / L N) atTop (𝓝 A))
    (hcH : Tendsto (fun N => c N * H N) atTop (𝓝 ℓ)) :
    Tendsto (fun N => c N * L N) atTop (𝓝 (ℓ / A)) := by
  have h1 : Tendsto (fun N => (c N * H N) * (H N / L N)⁻¹) atTop (𝓝 (ℓ * A⁻¹)) :=
    hcH.mul (hH.inv₀ hA)
  rw [div_eq_mul_inv]
  refine h1.congr' ?_
  filter_upwards [hH.eventually_ne hA] with N hne
  have hL0 : L N ≠ 0 := by
    intro h
    exact hne (by rw [h, div_zero])
  have hH0 : H N ≠ 0 := by
    intro h
    exact hne (by rw [h, zero_div])
  field_simp

/-- **A compensated normalizer transports a normalized limit.**  If `H/L → A ≠ 0` and `c · L → δ`,
then `c · H → δ · A`. -/
theorem tendsto_mul_of_tendsto_ratio {A δ : ℝ} (hA : A ≠ 0) (H c L : ℝ → ℝ)
    (hH : Tendsto (fun N => H N / L N) atTop (𝓝 A))
    (hc : Tendsto (fun N => c N * L N) atTop (𝓝 δ)) :
    Tendsto (fun N => c N * H N) atTop (𝓝 (δ * A)) := by
  have h1 : Tendsto (fun N => (c N * L N) * (H N / L N)) atTop (𝓝 (δ * A)) := hc.mul hH
  refine h1.congr' ?_
  filter_upwards [hH.eventually_ne hA] with N hne
  have hL0 : L N ≠ 0 := by
    intro h
    exact hne (by rw [h, div_zero])
  field_simp

/-- **Cross-system blindness.**  Two aperture families with the same nonzero normalized limit
against a common scale are indistinguishable by multiplicative regularization: any normalizer
making one converge makes the other converge, to the same limit. -/
theorem tendsto_mul_cross_system {A ℓ : ℝ} (hA : A ≠ 0) (H H' c L : ℝ → ℝ)
    (hH : Tendsto (fun N => H N / L N) atTop (𝓝 A))
    (hH' : Tendsto (fun N => H' N / L N) atTop (𝓝 A))
    (hcH : Tendsto (fun N => c N * H N) atTop (𝓝 ℓ)) :
    Tendsto (fun N => c N * H' N) atTop (𝓝 ℓ) := by
  have hδ := tendsto_normalizer_of_tendsto_ratio hA H c L hH hcH
  have h := tendsto_mul_of_tendsto_ratio hA H' c L hH' hδ
  rwa [div_mul_cancel₀ ℓ hA] at h

/-- **The regularized limits coincide.**  Stated as an equality of limits rather than as a
convergence statement. -/
theorem regularized_limit_eq {A ℓ ℓ' : ℝ} (hA : A ≠ 0) (H H' c L : ℝ → ℝ)
    (hH : Tendsto (fun N => H N / L N) atTop (𝓝 A))
    (hH' : Tendsto (fun N => H' N / L N) atTop (𝓝 A))
    (hcH : Tendsto (fun N => c N * H N) atTop (𝓝 ℓ))
    (hcH' : Tendsto (fun N => c N * H' N) atTop (𝓝 ℓ')) :
    ℓ = ℓ' :=
  tendsto_nhds_unique (tendsto_mul_cross_system hA H H' c L hH hH' hcH) hcH'

/-- **Blindness across a whole family of systems.**  Every member of a family of aperture families
sharing one normalized limit produces the same regularized limit. -/
theorem regularized_limit_const_on_family {ι : Type*} {A : ℝ} (hA : A ≠ 0)
    (H : ι → ℝ → ℝ) (c L : ℝ → ℝ) (ℓ : ι → ℝ)
    (hH : ∀ i, Tendsto (fun N => H i N / L N) atTop (𝓝 A))
    (hcH : ∀ i, Tendsto (fun N => c N * H i N) atTop (𝓝 (ℓ i))) :
    ∀ i j, ℓ i = ℓ j := fun i j =>
  regularized_limit_eq hA (H i) (H j) c L (hH i) (hH j) (hcH i) (hcH j)

/-! ## Truncated geometric corrections -/

/-- The number of powers `q^k` with `k ≥ 1` not exceeding `N`. -/
noncomputable def geomCount (q N : ℝ) : ℕ := ⌊Real.log N / Real.log q⌋₊

/-- The weight the generator `q` contributes to the Mertens sum below its `n`-th power. -/
noncomputable def geomTail (q : ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, q⁻¹ ^ (k + 1)

/-- **The generator's contribution converges.**  A single generalized prime contributes a
convergent geometric series to the Mertens sum. -/
theorem tendsto_geomTail {q : ℝ} (hq : 1 < q) :
    Tendsto (fun n : ℕ => geomTail q n) atTop (𝓝 (q - 1)⁻¹) := by
  have hq0 : (0 : ℝ) < q := lt_trans zero_lt_one hq
  have hinv_nonneg : (0 : ℝ) ≤ q⁻¹ := le_of_lt (inv_pos.mpr hq0)
  have hinv_lt : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hgeom : HasSum (fun n : ℕ => q⁻¹ ^ n) (1 - q⁻¹)⁻¹ :=
    hasSum_geometric_of_lt_one hinv_nonneg hinv_lt
  have hpart : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, q⁻¹ ^ k) atTop (𝓝 (1 - q⁻¹)⁻¹) :=
    hgeom.tendsto_sum_nat
  have hscaled : Tendsto (fun n : ℕ => q⁻¹ * ∑ k ∈ Finset.range n, q⁻¹ ^ k) atTop
      (𝓝 (q⁻¹ * (1 - q⁻¹)⁻¹)) := hpart.const_mul _
  have hval : q⁻¹ * (1 - q⁻¹)⁻¹ = (q - 1)⁻¹ := by
    have hq1 : q - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hq)
    field_simp
  rw [hval] at hscaled
  refine hscaled.congr fun n => ?_
  rw [geomTail, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The aperture count of a generator diverges. -/
theorem tendsto_geomCount {q : ℝ} (hq : 1 < q) :
    Tendsto (fun N : ℝ => geomCount q N) atTop atTop := by
  have hlogq : 0 < Real.log q := Real.log_pos hq
  have h1 : Tendsto (fun N : ℝ => Real.log N / Real.log q) atTop atTop := by
    simpa [div_eq_mul_inv] using
      Real.tendsto_log_atTop.atTop_mul_const (inv_pos.mpr hlogq)
  exact tendsto_nat_floor_atTop.comp h1

/-- The generator's contribution, read at the aperture, converges. -/
theorem tendsto_geomTail_geomCount {q : ℝ} (hq : 1 < q) :
    Tendsto (fun N : ℝ => geomTail q (geomCount q N)) atTop (𝓝 (q - 1)⁻¹) :=
  (tendsto_geomTail hq).comp (tendsto_geomCount hq)

/-! ## Mertens-normality under a generator swap -/

/-- A weighted prime-power count is *Mertens-normal* with constant `C` when it differs from
`log N` by `C + o(1)`. -/
def MertensNormal (S : ℝ → ℝ) (C : ℝ) : Prop :=
  Tendsto (fun N => S N - Real.log N) atTop (𝓝 C)

/-- The Mertens sum of the system obtained by deleting the generator `2` and adjoining `3`. -/
noncomputable def swapMertens (S : ℝ → ℝ) (N : ℝ) : ℝ :=
  S N - Real.log 2 * geomTail 2 (geomCount 2 N) + Real.log 3 * geomTail 3 (geomCount 3 N)

/-- **Mertens-normality survives the generator swap.**  Both corrections are convergent geometric
series, so the swapped system is Mertens-normal with the constant shifted by `log 3/2 − log 2`. -/
theorem mertensNormal_swapMertens {S : ℝ → ℝ} {C : ℝ} (hS : MertensNormal S C) :
    MertensNormal (swapMertens S) (C - Real.log 2 + Real.log 3 / 2) := by
  have h2 : Tendsto (fun N : ℝ => geomTail 2 (geomCount 2 N)) atTop (𝓝 ((2 : ℝ) - 1)⁻¹) :=
    tendsto_geomTail_geomCount (by norm_num)
  have h3 : Tendsto (fun N : ℝ => geomTail 3 (geomCount 3 N)) atTop (𝓝 ((3 : ℝ) - 1)⁻¹) :=
    tendsto_geomTail_geomCount (by norm_num)
  have h2' : Tendsto (fun N : ℝ => Real.log 2 * geomTail 2 (geomCount 2 N)) atTop
      (𝓝 (Real.log 2)) := by
    have := h2.const_mul (Real.log 2)
    norm_num at this
    exact this
  have h3' : Tendsto (fun N : ℝ => Real.log 3 * geomTail 3 (geomCount 3 N)) atTop
      (𝓝 (Real.log 3 / 2)) := by
    have := h3.const_mul (Real.log 3)
    norm_num at this
    simpa [div_eq_mul_inv, mul_comm] using this
  have := (hS.sub h2').add h3'
  refine this.congr fun N => ?_
  simp [swapMertens]
  ring

/-! ## The swapped system has a different zero set -/

open Complex

/-- The frequency `2πi/log 2`: the generator `2` is invisible to the swapped system there. -/
noncomputable def genFreq : ℂ := ((2 * Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I

theorem log_two_ne_zero : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))

theorem genFreq_eq : genFreq = 2 * (Real.pi : ℂ) * Complex.I / (Real.log 2 : ℂ) := by
  have h : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr log_two_ne_zero
  rw [genFreq]
  push_cast
  field_simp

theorem genFreq_re : genFreq.re = 0 := by
  rw [genFreq, Complex.mul_I_re, Complex.ofReal_im, neg_zero]

theorem genFreq_im : genFreq.im = 2 * Real.pi / Real.log 2 := by
  rw [genFreq, Complex.mul_I_im, Complex.ofReal_re]

/-- **The generator `2` is invisible at `s₀`.**  The Euler factor of `2` vanishes there. -/
theorem cpow_two_genFreq : (2 : ℂ) ^ (-genFreq) = 1 := by
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hne : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr log_two_ne_zero
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ) ≠ 0), hlog, genFreq_eq]
  have hkey : ((Real.log 2 : ℝ) : ℂ) * -(2 * (Real.pi : ℂ) * Complex.I / (Real.log 2 : ℂ))
      = -(2 * (Real.pi : ℂ) * Complex.I) := by
    field_simp
  rw [hkey, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

theorem one_sub_cpow_two_genFreq : 1 - (2 : ℂ) ^ (-genFreq) = 0 := by
  rw [cpow_two_genFreq, sub_self]

/-- `log 3 / log 2` lies strictly between `1` and `2`, hence is not an integer. -/
theorem log_three_div_log_two_not_int (n : ℤ) : Real.log 3 / Real.log 2 ≠ (n : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlow : (1 : ℝ) < Real.log 3 / Real.log 2 := by
    rw [lt_div_iff₀ hlog2]
    simpa using Real.log_lt_log (by norm_num) (by norm_num : (2:ℝ) < 3)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hhigh : Real.log 3 / Real.log 2 < 2 := by
    rw [div_lt_iff₀ hlog2]
    calc Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
      _ = 2 * Real.log 2 := hlog4
  intro h
  rw [h] at hlow hhigh
  have h1 : (1 : ℤ) < n := by exact_mod_cast hlow
  have h2 : n < (2 : ℤ) := by exact_mod_cast hhigh
  omega

/-- **The generator `3` is not invisible at `s₀`.**  Its Euler factor stays away from the pole. -/
theorem cpow_three_genFreq_ne_one : (3 : ℂ) ^ (-genFreq) ≠ 1 := by
  have hlog : Complex.log 3 = ((Real.log 3 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  have hne2 : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr log_two_ne_zero
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ) ≠ 0), hlog, genFreq_eq]
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have htwopi : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp [hpi, Complex.I_ne_zero]
  have hmul : (-(((Real.log 3 : ℝ) : ℂ) / ((Real.log 2 : ℝ) : ℂ))) * (2 * (Real.pi : ℂ) * Complex.I)
      = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [← hn]
    field_simp
  have hkey : -(((Real.log 3 : ℝ) : ℂ) / ((Real.log 2 : ℝ) : ℂ)) = (n : ℂ) :=
    mul_right_cancel₀ htwopi hmul
  have hreal : -(Real.log 3 / Real.log 2) = (n : ℝ) := by
    have hc : ((-(Real.log 3 / Real.log 2) : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by
      push_cast
      exact hkey
    exact_mod_cast hc
  refine log_three_div_log_two_not_int (-n) ?_
  push_cast
  linarith

theorem one_sub_cpow_three_genFreq_ne_zero : 1 - (3 : ℂ) ^ (-genFreq) ≠ 0 := by
  intro h
  exact cpow_three_genFreq_ne_one (by linear_combination -h)

/-- **`ζ` does not vanish at `s₀`.**  The functional equation transports the value to the line
`Re s = 1`, where `ζ`, `Γ`, the exponential factor and the cosine are all nonzero. -/
theorem riemannZeta_genFreq_ne_zero : riemannZeta genFreq ≠ 0 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hapos : 0 < 2 * Real.pi / Real.log 2 := by positivity
  set s : ℂ := 1 - genFreq with hsdef
  have hsre : s.re = 1 := by simp [hsdef, genFreq_re]
  have hsim : s.im = -(2 * Real.pi / Real.log 2) := by simp [hsdef, genFreq_im]
  have hsim_ne : s.im ≠ 0 := by
    rw [hsim]
    exact neg_ne_zero.mpr (ne_of_gt hapos)
  have hne_nat : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n hn
    apply hsim_ne
    rw [hn]
    simp
  have hs1 : s ≠ 1 := by
    intro h
    apply hsim_ne
    rw [h]
    simp
  have hEq := riemannZeta_one_sub hne_nat hs1
  have h1s : (1 : ℂ) - s = genFreq := by rw [hsdef]; ring
  rw [h1s] at hEq
  rw [hEq]
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hsre])
  have hg : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hne_nat
  have hpow : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    refine Complex.cpow_ne_zero_iff.mpr (Or.inl ?_)
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simp [hpi]
  have hcos : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    refine Complex.cos_ne_zero_iff.mpr fun k => ?_
    intro hk
    have him : ((Real.pi : ℂ) * s / 2).im = Real.pi * s.im / 2 := by
      simp [Complex.mul_im]
    have him' : ((2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2).im = 0 := by
      simp [Complex.mul_im, Complex.add_im]
    rw [hk, him'] at him
    have hzero : Real.pi * s.im = 0 := by linarith
    rcases mul_eq_zero.mp hzero with h | h
    · exact Real.pi_ne_zero h
    · exact hsim_ne h
  simp only [ne_eq, mul_eq_zero, not_or]
  exact ⟨⟨⟨⟨by norm_num, hpow⟩, hg⟩, hcos⟩, hz⟩

/-! ### The swapped system's zeta function -/

/-- The generator `2` of the rational primes. -/
def primeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩

theorem primeTwo_cast : ((primeTwo : ℕ) : ℂ) = 2 := by norm_num [primeTwo]

/-- The Euler factor family of the system obtained from the rational primes by deleting the
generator `2`. -/
noncomputable def deletedEulerFactor (s : ℂ) (p : Nat.Primes) : ℂ :=
  if p = primeTwo then 1 else (1 - (p : ℂ) ^ (-s))⁻¹

/-- The zeta function of the system obtained from the rational primes by deleting the generator
`2` and adjoining a second copy of `3`. -/
noncomputable def swappedZeta (s : ℂ) : ℂ :=
  riemannZeta s * (1 - (2 : ℂ) ^ (-s)) * (1 - (3 : ℂ) ^ (-s))⁻¹

/-- Deleting one factor from a convergent product divides the value by that factor. -/
theorem hasProd_ite_of_hasProd {ι M : Type*} [DecidableEq ι] [CommGroupWithZero M]
    [TopologicalSpace M] [ContinuousMul M] {f : ι → M} {a : M} (hf : HasProd f a) (b : ι)
    (hb : f b ≠ 0) : HasProd (fun i => if i = b then 1 else f i) (a * (f b)⁻¹) := by
  have h : Tendsto (fun s : Finset ι => (∏ i ∈ s, f i) * (f b)⁻¹) atTop (𝓝 (a * (f b)⁻¹)) :=
    hf.mul_const _
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop ({b} : Finset ι)] with t ht
  have hbs : b ∈ t := ht (Finset.mem_singleton_self b)
  have h1 : ∏ i ∈ t, f i = f b * ∏ i ∈ t.erase b, f i := (Finset.mul_prod_erase t f hbs).symm
  have h2 : ∏ i ∈ t, (if i = b then (1 : M) else f i)
      = (if b = b then (1 : M) else f b)
        * ∏ i ∈ t.erase b, (if i = b then (1 : M) else f i) :=
    (Finset.mul_prod_erase t (fun i => if i = b then (1 : M) else f i) hbs).symm
  have h3 : ∏ i ∈ t.erase b, (if i = b then (1 : M) else f i) = ∏ i ∈ t.erase b, f i :=
    Finset.prod_congr rfl fun i hi => if_neg (Finset.ne_of_mem_erase hi)
  rw [h1, h2, h3, if_pos rfl, one_mul, mul_comm (f b), mul_assoc, mul_inv_cancel₀ hb, mul_one]

theorem one_sub_two_cpow_ne_zero {s : ℂ} (hs : 1 < s.re) : 1 - (2 : ℂ) ^ (-s) ≠ 0 := by
  have hnorm : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    simp
  have hlt : ‖(2 : ℂ) ^ (-s)‖ < 1 := by
    rw [hnorm]
    have : (-s.re) < 0 := by linarith
    calc (2 : ℝ) ^ (-s.re) < (2 : ℝ) ^ (0 : ℝ) := by
          exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) this
      _ = 1 := Real.rpow_zero 2
  intro h
  have : (2 : ℂ) ^ (-s) = 1 := by linear_combination -h
  rw [this] at hlt
  simp at hlt

/-- **The Euler product of the swapped system.**  On the half-plane of absolute convergence the
system obtained by deleting `2` has zeta function `ζ(s)(1 − 2^{-s})`. -/
theorem hasProd_deletedEulerFactor {s : ℂ} (hs : 1 < s.re) :
    HasProd (deletedEulerFactor s) (riemannZeta s * (1 - (2 : ℂ) ^ (-s))) := by
  have hEuler := riemannZeta_eulerProduct_hasProd hs
  have hfb : (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-s))⁻¹) primeTwo
      = (1 - (2 : ℂ) ^ (-s))⁻¹ := by
    show (1 - ((primeTwo : ℕ) : ℂ) ^ (-s))⁻¹ = (1 - (2 : ℂ) ^ (-s))⁻¹
    rw [primeTwo_cast]
  have hbne : (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-s))⁻¹) primeTwo ≠ 0 := by
    rw [hfb]
    exact inv_ne_zero (one_sub_two_cpow_ne_zero hs)
  have h := hasProd_ite_of_hasProd hEuler primeTwo hbne
  rw [primeTwo_cast, inv_inv] at h
  exact h

theorem swappedZeta_eq_tprod {s : ℂ} (hs : 1 < s.re) :
    swappedZeta s = (∏' p : Nat.Primes, deletedEulerFactor s p) * (1 - (3 : ℂ) ^ (-s))⁻¹ := by
  rw [(hasProd_deletedEulerFactor hs).tprod_eq, swappedZeta]

/-- **The swapped system vanishes at `s₀`.** -/
theorem swappedZeta_genFreq : swappedZeta genFreq = 0 := by
  rw [swappedZeta, one_sub_cpow_two_genFreq, mul_zero, zero_mul]

/-- **The zero sets differ.**  `s₀ = 2πi/log 2` is a zero of the swapped system's zeta function,
its Euler factor at `3` is regular there, and `ζ(s₀) ≠ 0`. -/
theorem zeroSets_differ :
    swappedZeta genFreq = 0 ∧ (1 - (3 : ℂ) ^ (-genFreq)) ≠ 0 ∧ riemannZeta genFreq ≠ 0 :=
  ⟨swappedZeta_genFreq, one_sub_cpow_three_genFreq_ne_zero, riemannZeta_genFreq_ne_zero⟩

end GaloisForLFunctions.HTGeometry.Beurling

namespace GaloisForLFunctions.HTGeometry.Beurling

open Filter Topology intervalIntegral MeasureTheory

/-! ## The prime log-jet Gram of a Mertens-normal system

The Gram entry `H_{k+1}(N) = ∑_{n ≤ N} Λ(n) n⁻¹ (log n)^{k+1}` is the Stieltjes integral of
`(log x)^{k+1}` against the Mertens sum `S`.  Writing `(log x)^{k+1}` as `∫_0^{log x} (k+1)u^k du`
and exchanging the order turns the entry into

`∫_0^{L} (k+1) u^k (S(N) − S(e^u)) du`,     `L = log N`,

which is the quantity studied here.  Mertens-normality says `S(x) − log x` stays within `M` of a
constant, so the inner bracket is `L − u` up to `2M`; the main term integrates to `L^{k+2}/(k+2)`
and the error contributes at most `2M L^{k+1}`.  Every Mertens-normal system therefore has the same
normalized limit `1/(k+2)`, which is exactly the hypothesis the cross-system blindness theorem
consumes. -/

/-- The layer-cake form of the prime log-jet Gram entry of exponent `k+1` at aperture `N`. -/
noncomputable def jetIntegral (S : ℝ → ℝ) (k : ℕ) (N : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..Real.log N, ((k : ℝ) + 1) * u ^ k * (S N - S (Real.exp u))

/-- The main term of the layer-cake integral. -/
theorem integral_layer_main (k : ℕ) (L : ℝ) :
    (∫ u in (0 : ℝ)..L, ((k : ℝ) + 1) * u ^ k * (L - u)) = L ^ (k + 2) / ((k : ℝ) + 2) := by
  have hc1 : IntervalIntegrable (fun u : ℝ => (((k : ℝ) + 1) * L) * u ^ k) volume 0 L :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hc2 : IntervalIntegrable (fun u : ℝ => ((k : ℝ) + 1) * u ^ (k + 1)) volume 0 L :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have h1 : (∫ u in (0 : ℝ)..L, u ^ k) = L ^ (k + 1) / ((k : ℝ) + 1) := by
    rw [integral_pow]
    simp
  have h2 : (∫ u in (0 : ℝ)..L, u ^ (k + 1)) = L ^ (k + 2) / ((k : ℝ) + 2) := by
    rw [integral_pow]
    push_cast
    rw [show k + 1 + 1 = k + 2 from rfl]
    simp
    ring_nf
  have hsplit : (fun u : ℝ => ((k : ℝ) + 1) * u ^ k * (L - u))
      = fun u : ℝ => (((k : ℝ) + 1) * L) * u ^ k - ((k : ℝ) + 1) * u ^ (k + 1) := by
    funext u
    ring
  rw [hsplit, intervalIntegral.integral_sub hc1 hc2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, h1, h2]
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hk2 : ((k : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

/-- The layer-cake integrand is integrable for any monotone Mertens sum. -/
theorem intervalIntegrable_jetIntegrand {S : ℝ → ℝ} (hmono : Monotone S) (k : ℕ) (N L : ℝ) :
    IntervalIntegrable (fun u : ℝ => ((k : ℝ) + 1) * u ^ k * (S N - S (Real.exp u)))
      volume 0 L := by
  have hS : IntervalIntegrable (fun u : ℝ => S (Real.exp u)) volume 0 L :=
    Monotone.intervalIntegrable (hmono.comp Real.exp_monotone)
  have hdiff : IntervalIntegrable (fun u : ℝ => S N - S (Real.exp u)) volume 0 L :=
    (intervalIntegrable_const (c := S N)).sub hS
  exact hdiff.continuousOn_mul (by fun_prop)

/-- **Lemma 2.1.**  For a Mertens-normal system the layer-cake Gram entry equals its main term
`L^{k+2}/(k+2)` up to `2M L^{k+1}`, where `M` bounds the Mertens defect. -/
theorem jetIntegral_sub_main_abs_le {S : ℝ → ℝ} {C M : ℝ} (hmono : Monotone S)
    (hbound : ∀ x : ℝ, 1 ≤ x → |S x - Real.log x - C| ≤ M) (k : ℕ) {N : ℝ} (hN : 1 ≤ N) :
    |jetIntegral S k N - (Real.log N) ^ (k + 2) / ((k : ℝ) + 2)|
      ≤ 2 * M * (Real.log N) ^ (k + 1) := by
  set L : ℝ := Real.log N with hLdef
  have hL : 0 ≤ L := Real.log_nonneg hN
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hbound 1 le_rfl)
  have hI2 : IntervalIntegrable (fun u : ℝ => ((k : ℝ) + 1) * u ^ k * (S N - S (Real.exp u)))
      volume 0 L := intervalIntegrable_jetIntegrand hmono k N L
  have hI1 : IntervalIntegrable (fun u : ℝ => ((k : ℝ) + 1) * u ^ k * (L - u)) volume 0 L :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hIE : IntervalIntegrable
      (fun u : ℝ => ((k : ℝ) + 1) * u ^ k * (S N - S (Real.exp u))
        - ((k : ℝ) + 1) * u ^ k * (L - u)) volume 0 L := hI2.sub hI1
  have hdecomp : jetIntegral S k N - L ^ (k + 2) / ((k : ℝ) + 2)
      = ∫ u in (0 : ℝ)..L, (((k : ℝ) + 1) * u ^ k * (S N - S (Real.exp u))
          - ((k : ℝ) + 1) * u ^ k * (L - u)) := by
    rw [intervalIntegral.integral_sub hI2 hI1, integral_layer_main k L, jetIntegral, ← hLdef]
  -- pointwise bound on the error integrand
  have hpt : ∀ u ∈ Set.Icc (0 : ℝ) L,
      |((k : ℝ) + 1) * u ^ k * (S N - S (Real.exp u)) - ((k : ℝ) + 1) * u ^ k * (L - u)|
        ≤ ((k : ℝ) + 1) * (2 * M) * u ^ k := by
    intro u hu
    obtain ⟨hu0, huL⟩ := hu
    have hexp : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu0
    have hb1 : |S N - L - C| ≤ M := hbound N hN
    have hb2 : |S (Real.exp u) - u - C| ≤ M := by
      have := hbound (Real.exp u) hexp
      rwa [Real.log_exp] at this
    have hE : ((k : ℝ) + 1) * u ^ k * (S N - S (Real.exp u)) - ((k : ℝ) + 1) * u ^ k * (L - u)
        = (((k : ℝ) + 1) * u ^ k) * ((S N - L - C) - (S (Real.exp u) - u - C)) := by
      ring
    rw [hE, abs_mul]
    have habs1 : |((k : ℝ) + 1) * u ^ k| = ((k : ℝ) + 1) * u ^ k := by
      rw [abs_of_nonneg (by positivity)]
    have habs2 : |(S N - L - C) - (S (Real.exp u) - u - C)| ≤ 2 * M := by
      calc |(S N - L - C) - (S (Real.exp u) - u - C)|
          ≤ |S N - L - C| + |S (Real.exp u) - u - C| := abs_sub _ _
        _ ≤ M + M := add_le_add hb1 hb2
        _ = 2 * M := by ring
    rw [habs1]
    calc ((k : ℝ) + 1) * u ^ k * |(S N - L - C) - (S (Real.exp u) - u - C)|
        ≤ ((k : ℝ) + 1) * u ^ k * (2 * M) := by
          exact mul_le_mul_of_nonneg_left habs2 (by positivity)
      _ = ((k : ℝ) + 1) * (2 * M) * u ^ k := by ring
  have hbnd : IntervalIntegrable (fun u : ℝ => ((k : ℝ) + 1) * (2 * M) * u ^ k) volume 0 L :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hstep : |∫ u in (0 : ℝ)..L, (((k : ℝ) + 1) * u ^ k * (S N - S (Real.exp u))
      - ((k : ℝ) + 1) * u ^ k * (L - u))|
      ≤ ∫ u in (0 : ℝ)..L, ((k : ℝ) + 1) * (2 * M) * u ^ k := by
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs hL) ?_
    exact intervalIntegral.integral_mono_on hL hIE.abs hbnd hpt
  have hval : (∫ u in (0 : ℝ)..L, ((k : ℝ) + 1) * (2 * M) * u ^ k) = 2 * M * L ^ (k + 1) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    simp
    field_simp
  rw [hdecomp]
  rw [hval] at hstep
  exact hstep

/-- **The normalized Gram limit is the same for every Mertens-normal system.**  The limit
`1/(k+2)` depends on the exponent only — not on the system, not on its Mertens constant, and not on
the size of its Mertens defect. -/
theorem tendsto_jetIntegral_ratio {S : ℝ → ℝ} {C M : ℝ} (hmono : Monotone S)
    (hbound : ∀ x : ℝ, 1 ≤ x → |S x - Real.log x - C| ≤ M) (k : ℕ) :
    Tendsto (fun N => jetIntegral S k N / (Real.log N) ^ (k + 2)) atTop
      (𝓝 (1 / ((k : ℝ) + 2))) := by
  have hk2 : ((k : ℝ) + 2) ≠ 0 := by positivity
  have hdiff : Tendsto
      (fun N => jetIntegral S k N / (Real.log N) ^ (k + 2) - 1 / ((k : ℝ) + 2)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (Tendsto.div_atTop (f := fun _ : ℝ => 2 * M)
      tendsto_const_nhds Real.tendsto_log_atTop)
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
    have hN1 : (1 : ℝ) ≤ N := le_trans (le_trans (by norm_num) (Real.add_one_le_exp 1)) hN
    have hL1 : (1 : ℝ) ≤ Real.log N := by
      have := Real.log_le_log (Real.exp_pos 1) hN
      rwa [Real.log_exp] at this
    have hLpos : (0 : ℝ) < Real.log N := lt_of_lt_of_le zero_lt_one hL1
    have hpow : (0 : ℝ) < (Real.log N) ^ (k + 2) := by positivity
    have hkey := jetIntegral_sub_main_abs_le hmono hbound k hN1
    have hrw : jetIntegral S k N / (Real.log N) ^ (k + 2) - 1 / ((k : ℝ) + 2)
        = (jetIntegral S k N - (Real.log N) ^ (k + 2) / ((k : ℝ) + 2))
          / (Real.log N) ^ (k + 2) := by
      field_simp
    rw [Real.norm_eq_abs, hrw, abs_div, abs_of_pos hpow, div_le_iff₀ hpow]
    calc |jetIntegral S k N - (Real.log N) ^ (k + 2) / ((k : ℝ) + 2)|
        ≤ 2 * M * (Real.log N) ^ (k + 1) := hkey
      _ ≤ 2 * M / Real.log N * (Real.log N) ^ (k + 2) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hLpos]
          have : (Real.log N) ^ (k + 1) * Real.log N = (Real.log N) ^ (k + 2) := by ring
          rw [mul_assoc, this]
  have := hdiff.add_const (1 / ((k : ℝ) + 2))
  simpa using this

/-- **Cross-system blindness for Mertens-normal Beurling systems.**  Any multiplicative
regularization convergent on one Mertens-normal system converges on every other, with the same
limit — regardless of the two systems' Mertens constants and defects. -/
theorem regularized_jet_limit_eq {S S' : ℝ → ℝ} {C M C' M' : ℝ} {c : ℝ → ℝ} {ℓ ℓ' : ℝ}
    (hmono : Monotone S) (hbound : ∀ x : ℝ, 1 ≤ x → |S x - Real.log x - C| ≤ M)
    (hmono' : Monotone S') (hbound' : ∀ x : ℝ, 1 ≤ x → |S' x - Real.log x - C'| ≤ M')
    (k : ℕ)
    (hc : Tendsto (fun N => c N * jetIntegral S k N) atTop (𝓝 ℓ))
    (hc' : Tendsto (fun N => c N * jetIntegral S' k N) atTop (𝓝 ℓ')) :
    ℓ = ℓ' := by
  have hA : (1 : ℝ) / ((k : ℝ) + 2) ≠ 0 := by positivity
  exact regularized_limit_eq hA (jetIntegral S k) (jetIntegral S' k) c
    (fun N => (Real.log N) ^ (k + 2))
    (tendsto_jetIntegral_ratio hmono hbound k) (tendsto_jetIntegral_ratio hmono' hbound' k) hc hc'

end GaloisForLFunctions.HTGeometry.Beurling

namespace GaloisForLFunctions.HTGeometry.Beurling

open Filter Topology intervalIntegral MeasureTheory Set

/-! ## From the Gram sum to the layer-cake integral

Writing `(log t)^{k+1} = ∫_0^{L} (k+1)u^k · [u < log t] du` for `1 ≤ t ≤ N` and exchanging the
finite sum with the integral turns the Gram entry of a Beurling system into the layer-cake integral
of the previous section.  The exchange is legitimate because each atom's integrand is a monotone
indicator times a polynomial, hence interval integrable. -/

/-- The layer-cake integrand of a single atom is interval integrable: a monotone indicator times a
polynomial. -/
theorem intervalIntegrable_layer_atom (k : ℕ) (a x y : ℝ) :
    IntervalIntegrable (fun u : ℝ => ((k : ℝ) + 1) * u ^ k * (if u < a then (1 : ℝ) else 0))
      volume x y := by
  have hanti : Antitone (fun u : ℝ => if u < a then (1 : ℝ) else 0) := by
    intro s t hst
    show (if t < a then (1 : ℝ) else 0) ≤ (if s < a then (1 : ℝ) else 0)
    by_cases ht : t < a
    · rw [if_pos ht, if_pos (lt_of_le_of_lt hst ht)]
    · rw [if_neg ht]
      split_ifs <;> norm_num
  exact hanti.intervalIntegrable.continuousOn_mul (by fun_prop)

/-- **The layer-cake weight of one atom.**  An atom of magnitude `exp a` with `0 ≤ a ≤ L`
contributes exactly `a^{k+1}` to the layer-cake integral over `[0, L]`. -/
theorem integral_layer_atom (k : ℕ) {a L : ℝ} (ha : 0 ≤ a) (haL : a ≤ L) :
    (∫ u in (0 : ℝ)..L, ((k : ℝ) + 1) * u ^ k * (if u < a then (1 : ℝ) else 0))
      = a ^ (k + 1) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_layer_atom k a 0 a) (intervalIntegrable_layer_atom k a a L)]
  have h1 : (∫ u in (0 : ℝ)..a, ((k : ℝ) + 1) * u ^ k * (if u < a then (1 : ℝ) else 0))
      = ∫ u in (0 : ℝ)..a, ((k : ℝ) + 1) * u ^ k := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton a)] with u hu hmem
    have hle : u ≤ a := by
      rcases Set.mem_uIoc.mp hmem with ⟨_, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · exact absurd (lt_of_lt_of_le h1 (le_trans h2 ha)) (lt_irrefl a)
    have hne : u ≠ a := by simpa using hu
    rw [if_pos (lt_of_le_of_ne hle hne), mul_one]
  have h2 : (∫ u in a..L, ((k : ℝ) + 1) * u ^ k * (if u < a then (1 : ℝ) else 0)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (0 : ℝ)) ?_,
      intervalIntegral.integral_zero]
    intro u hu
    rw [Set.uIcc_of_le haL] at hu
    show ((k : ℝ) + 1) * u ^ k * (if u < a then (1 : ℝ) else 0) = 0
    rw [if_neg (not_lt.mpr hu.1), mul_zero]
  rw [h1, h2, add_zero, intervalIntegral.integral_const_mul, integral_pow]
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  simp
  field_simp

/-- A Beurling system: generalized prime powers of magnitude at least one, carrying nonnegative
weights, with finitely many atoms below every threshold. -/
structure System (ι : Type*) where
  /-- The magnitude of a generalized prime power. -/
  mag : ι → ℝ
  /-- Its weight, `Λ(n)/n` for the rational primes. -/
  weight : ι → ℝ
  one_le_mag : ∀ i, 1 ≤ mag i
  weight_nonneg : ∀ i, 0 ≤ weight i
  finite_below : ∀ x : ℝ, {i | mag i ≤ x}.Finite

namespace System

variable {ι : Type*} (B : System ι)

/-- The aperture: the atoms of magnitude at most `x`. -/
noncomputable def aperture (x : ℝ) : Finset ι := (B.finite_below x).toFinset

theorem mem_aperture {x : ℝ} {i : ι} : i ∈ B.aperture x ↔ B.mag i ≤ x := by
  rw [aperture, Set.Finite.mem_toFinset]
  rfl

theorem aperture_subset {x y : ℝ} (hxy : x ≤ y) : B.aperture x ⊆ B.aperture y := by
  intro i hi
  rw [mem_aperture] at hi ⊢
  exact le_trans hi hxy

/-- The Mertens sum of the system at aperture `x`. -/
noncomputable def mertens (x : ℝ) : ℝ := ∑ i ∈ B.aperture x, B.weight i

/-- The prime log-jet Gram entry of exponent `k+1` at aperture `x`. -/
noncomputable def jet (k : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ B.aperture x, B.weight i * Real.log (B.mag i) ^ (k + 1)

theorem monotone_mertens : Monotone B.mertens := by
  intro x y hxy
  exact Finset.sum_le_sum_of_subset_of_nonneg (B.aperture_subset hxy)
    (fun i _ _ => B.weight_nonneg i)

/-- The Mertens increment between two apertures counts exactly the atoms in between. -/
theorem mertens_sub {N u : ℝ} (hu : Real.exp u ≤ N) :
    B.mertens N - B.mertens (Real.exp u)
      = ∑ i ∈ B.aperture N,
          B.weight i * (if u < Real.log (B.mag i) then (1 : ℝ) else 0) := by
  classical
  have hsub : B.aperture (Real.exp u) ⊆ B.aperture N := B.aperture_subset hu
  rw [mertens, mertens, ← Finset.sum_sdiff_eq_sub hsub]
  have hset : B.aperture N \ B.aperture (Real.exp u)
      = (B.aperture N).filter (fun i => u < Real.log (B.mag i)) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_filter, mem_aperture]
    have hmag : 0 < B.mag i := lt_of_lt_of_le zero_lt_one (B.one_le_mag i)
    constructor
    · rintro ⟨hiN, hnot⟩
      exact ⟨hiN, (Real.lt_log_iff_exp_lt hmag).mpr (not_le.mp hnot)⟩
    · rintro ⟨hiN, hlt⟩
      exact ⟨hiN, not_le.mpr ((Real.lt_log_iff_exp_lt hmag).mp hlt)⟩
  rw [hset, Finset.sum_filter]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> ring

/-- **The Gram entry is the layer-cake integral.**  For every aperture `N ≥ 1` the prime log-jet
Gram entry of exponent `k+1` equals the layer-cake integral of the Mertens sum. -/
theorem jet_eq_jetIntegral (k : ℕ) {N : ℝ} (hN : 1 ≤ N) :
    B.jet k N = jetIntegral B.mertens k N := by
  classical
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hL : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN
  have hjet : B.jet k N = ∑ i ∈ B.aperture N, B.weight i * Real.log (B.mag i) ^ (k + 1) := rfl
  rw [hjet, jetIntegral]
  have hcongr : EqOn
      (fun u : ℝ => ((k : ℝ) + 1) * u ^ k * (B.mertens N - B.mertens (Real.exp u)))
      (fun u : ℝ => ∑ i ∈ B.aperture N,
        B.weight i * (((k : ℝ) + 1) * u ^ k
          * (if u < Real.log (B.mag i) then (1 : ℝ) else 0)))
      (uIcc 0 (Real.log N)) := by
    intro u hu
    rw [Set.uIcc_of_le hL] at hu
    have hexpu : Real.exp u ≤ N := by
      rw [← Real.exp_log hNpos]
      exact Real.exp_le_exp.mpr hu.2
    simp only
    rw [B.mertens_sub hexpu, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_finsetSum
      (fun i _ => (intervalIntegrable_layer_atom k (Real.log (B.mag i)) 0 (Real.log N)).const_mul _)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hmag1 : 1 ≤ B.mag i := B.one_le_mag i
  have ha : 0 ≤ Real.log (B.mag i) := Real.log_nonneg hmag1
  have haL : Real.log (B.mag i) ≤ Real.log N :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hmag1) ((B.mem_aperture).mp hi)
  rw [intervalIntegral.integral_const_mul, integral_layer_atom k ha haL]

/-- **Lemma 2.1.**  For a Mertens-normal Beurling system the Gram entry of exponent `k+1` equals
`L^{k+2}/(k+2)` up to `2M L^{k+1}`, where `M` bounds the Mertens defect. -/
theorem jet_sub_main_abs_le {C M : ℝ}
    (hbound : ∀ x : ℝ, 1 ≤ x → |B.mertens x - Real.log x - C| ≤ M) (k : ℕ) {N : ℝ} (hN : 1 ≤ N) :
    |B.jet k N - (Real.log N) ^ (k + 2) / ((k : ℝ) + 2)| ≤ 2 * M * (Real.log N) ^ (k + 1) := by
  rw [B.jet_eq_jetIntegral k hN]
  exact jetIntegral_sub_main_abs_le B.monotone_mertens hbound k hN

/-- **The normalized Gram limit of a Mertens-normal Beurling system is `1/(k+2)`.**  It depends on
the exponent alone: not on the system, not on its Mertens constant, not on its defect. -/
theorem tendsto_jet_ratio {C M : ℝ}
    (hbound : ∀ x : ℝ, 1 ≤ x → |B.mertens x - Real.log x - C| ≤ M) (k : ℕ) :
    Tendsto (fun N => B.jet k N / (Real.log N) ^ (k + 2)) atTop (𝓝 (1 / ((k : ℝ) + 2))) := by
  have hmain := tendsto_jetIntegral_ratio B.monotone_mertens hbound k
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  rw [B.jet_eq_jetIntegral k hN]

end System

/-- **Theorem 3.1, cross-system blindness of multiplicative regularization.**  Let `B` and `B'` be
Mertens-normal Beurling systems, and let a single multiplicative regularization `c` make both prime
log-jet Gram entries of exponent `k+1` converge.  Then the two limits are equal.  The limit is
therefore a function of the normalizer alone and carries no information distinguishing the two
systems. -/
theorem regularized_jet_limit_eq_of_systems {ι ι' : Type*} (B : System ι) (B' : System ι')
    {C M C' M' : ℝ} {c : ℝ → ℝ} {ℓ ℓ' : ℝ}
    (hbound : ∀ x : ℝ, 1 ≤ x → |B.mertens x - Real.log x - C| ≤ M)
    (hbound' : ∀ x : ℝ, 1 ≤ x → |B'.mertens x - Real.log x - C'| ≤ M')
    (k : ℕ)
    (hc : Tendsto (fun N => c N * B.jet k N) atTop (𝓝 ℓ))
    (hc' : Tendsto (fun N => c N * B'.jet k N) atTop (𝓝 ℓ')) :
    ℓ = ℓ' := by
  have hA : (1 : ℝ) / ((k : ℝ) + 2) ≠ 0 := by positivity
  exact regularized_limit_eq hA (B.jet k) (B'.jet k) c (fun N => (Real.log N) ^ (k + 2))
    (B.tendsto_jet_ratio hbound k) (B'.tendsto_jet_ratio hbound' k) hc hc'

end GaloisForLFunctions.HTGeometry.Beurling
