import Mathlib

/-!
# Log-scale exponents and the Newton edge

Two independent facts behind the selection of a Newton edge from an asymptotic relation.

* **No cancellation of a strict maximum.**  Measure a family of terms on the logarithmic scale set by
  a radius `ρ → ∞`: `f` has exponent `a` when `log ‖f‖ / log ρ → a`.  If one term of a finite sum has
  strictly the largest exponent, all the others are `o` of it, so the sum cannot vanish along the
  filter.  Contrapositively, a vanishing finite sum forces the maximal exponent to be attained at
  least twice — the maximal face of the Newton polygon is an edge, not a vertex.  The `o(1)` in the
  measured exponents is harmless: only the fixed gap between the largest weight and the rest is used.

* **An edge polynomial has a nonzero root.**  A complex polynomial with at least two nonzero
  coefficients factors as `X^m q` with `q(0) ≠ 0` and `deg q ≥ 1`, so a root of `q` is a nonzero root
  of the polynomial.

Together these say: an asymptotic relation whose measured weights have a unique maximum is
impossible, and once the maximum is attained twice the edge equation has a genuine nonzero solution.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Asymptotics

/-! ## Log-scale exponents -/

/-- `f` has logarithmic-scale exponent `a` relative to the radius `ρ` along `l`: it is eventually
nonzero and `log ‖f‖ / log ρ → a`. -/
def HasLogScaleExponent {α : Type*} (l : Filter α) (ρ : α → ℝ) (f : α → ℂ) (a : ℝ) : Prop :=
  (∀ᶠ x in l, f x ≠ 0) ∧
    Tendsto (fun x => Real.log ‖f x‖ / Real.log (ρ x)) l (nhds a)

/-- **A strictly smaller exponent is negligible.**  Only the gap between the two exponents is used,
so the `o(1)` in each measured exponent cannot close it. -/
theorem isLittleO_of_hasLogScaleExponent_lt
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {f g : α → ℂ} {a b : ℝ} (hf : HasLogScaleExponent l ρ f a)
    (hg : HasLogScaleExponent l ρ g b) (hab : a < b) :
    f =o[l] g := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  set ε : ℝ := (b - a) / 3 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hlogρ : Tendsto (fun x => Real.log (ρ x)) l atTop :=
    Real.tendsto_log_atTop.comp hρ
  have h1 : ∀ᶠ x in l, Real.log ‖f x‖ / Real.log (ρ x) < a + ε :=
    hf.2.eventually_lt_const (by linarith)
  have h2 : ∀ᶠ x in l, b - ε < Real.log ‖g x‖ / Real.log (ρ x) :=
    hg.2.eventually_const_lt (by linarith)
  have h3 : ∀ᶠ x in l, Real.log c⁻¹ / ε < Real.log (ρ x) := hlogρ.eventually_gt_atTop _
  have h4 : ∀ᶠ x in l, (0 : ℝ) < Real.log (ρ x) := hlogρ.eventually_gt_atTop 0
  filter_upwards [h1, h2, h3, h4, hf.1, hg.1] with x hx1 hx2 hx3 hx4 hfx hgx
  have hfn : (0 : ℝ) < ‖f x‖ := norm_pos_iff.mpr hfx
  have hgn : (0 : ℝ) < ‖g x‖ := norm_pos_iff.mpr hgx
  have hflog : Real.log ‖f x‖ < (a + ε) * Real.log (ρ x) := (div_lt_iff₀ hx4).mp hx1
  have hglog : (b - ε) * Real.log (ρ x) < Real.log ‖g x‖ := (lt_div_iff₀ hx4).mp hx2
  have hclog : -(ε * Real.log (ρ x)) < Real.log c := by
    have := (div_lt_iff₀ hεpos).mp hx3
    rw [Real.log_inv] at this
    linarith
  have hgap : (a + ε) * Real.log (ρ x) - (b - ε) * Real.log (ρ x)
      = -(ε * Real.log (ρ x)) := by
    rw [hεdef]; ring
  have hkey : Real.log ‖f x‖ < Real.log (c * ‖g x‖) := by
    rw [Real.log_mul (ne_of_gt hc) (ne_of_gt hgn)]
    have : Real.log ‖f x‖ - Real.log ‖g x‖ < -(ε * Real.log (ρ x)) := by
      calc Real.log ‖f x‖ - Real.log ‖g x‖
          < (a + ε) * Real.log (ρ x) - (b - ε) * Real.log (ρ x) := by linarith
        _ = -(ε * Real.log (ρ x)) := hgap
    linarith
  have hlt : ‖f x‖ < c * ‖g x‖ := by
    have hpos : (0 : ℝ) < c * ‖g x‖ := mul_pos hc hgn
    exact (Real.log_lt_log_iff hfn hpos).mp hkey
  exact le_of_lt hlt

/-- **The maximal weight cannot be attained once.**  A finite sum of terms with measured log-scale
exponents that vanishes along the filter cannot have a strict maximum. -/
theorem not_eventually_sum_eq_zero_of_unique_max
    {α ι : Type*} {l : Filter α} [l.NeBot] {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    (s : Finset ι) (w : ι → ℝ) (g : ι → α → ℂ)
    (hg : ∀ i ∈ s, HasLogScaleExponent l ρ (g i) (w i))
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hmax : ∀ i ∈ s, i ≠ i₀ → w i < w i₀) :
    ¬ (∀ᶠ x in l, ∑ i ∈ s, g i x = 0) := by
  classical
  intro hsum
  have hrest : (fun x => ∑ i ∈ s.erase i₀, g i x) =o[l] (g i₀) := by
    refine Asymptotics.IsLittleO.sum fun i hi => ?_
    have hmem : i ∈ s := Finset.mem_of_mem_erase hi
    exact isLittleO_of_hasLogScaleExponent_lt hρ (hg i hmem) (hg i₀ hi₀)
      (hmax i hmem (Finset.ne_of_mem_erase hi))
  have hhalf := hrest.def (c := 1 / 2) (by norm_num)
  have hsplit : ∀ x, ∑ i ∈ s, g i x = g i₀ x + ∑ i ∈ s.erase i₀, g i x := fun x =>
    (Finset.add_sum_erase s (fun i => g i x) hi₀).symm
  have hcontra : ∀ᶠ x in l, False := by
    filter_upwards [hsum, hhalf, (hg i₀ hi₀).1] with x hx hxo hx0
    rw [hsplit x] at hx
    have heq : ∑ i ∈ s.erase i₀, g i x = -(g i₀ x) := by linear_combination hx
    rw [heq, norm_neg] at hxo
    have hpos : (0 : ℝ) < ‖g i₀ x‖ := norm_pos_iff.mpr hx0
    linarith
  exact (Filter.eventually_false_iff_eq_bot.mp hcontra ▸ ‹l.NeBot›.ne) rfl

/-! ## The weight calculus -/

/-- A nonzero constant has log-scale exponent zero. -/
theorem hasLogScaleExponent_const
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop) {c : ℂ} (hc : c ≠ 0) :
    HasLogScaleExponent l ρ (fun _ => c) 0 := by
  refine ⟨Filter.Eventually.of_forall fun _ => hc, ?_⟩
  have hlogρ : Tendsto (fun x => Real.log (ρ x)) l atTop :=
    Real.tendsto_log_atTop.comp hρ
  exact (tendsto_const_nhds (x := Real.log ‖c‖) (f := l)).div_atTop hlogρ

/-- **Weights add under multiplication.** -/
theorem HasLogScaleExponent.mul
    {α : Type*} {l : Filter α} {ρ : α → ℝ} {f g : α → ℂ} {a b : ℝ}
    (hf : HasLogScaleExponent l ρ f a) (hg : HasLogScaleExponent l ρ g b) :
    HasLogScaleExponent l ρ (fun x => f x * g x) (a + b) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.1, hg.1] with x hx hy using mul_ne_zero hx hy
  · refine Filter.Tendsto.congr' ?_ (hf.2.add hg.2)
    filter_upwards [hf.1, hg.1] with x hx hy
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy), add_div]

/-- **Weights scale under powers.** -/
theorem HasLogScaleExponent.pow
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop) {f : α → ℂ} {a : ℝ}
    (hf : HasLogScaleExponent l ρ f a) (n : ℕ) :
    HasLogScaleExponent l ρ (fun x => f x ^ n) ((n : ℝ) * a) := by
  induction n with
  | zero => simpa using hasLogScaleExponent_const hρ (c := (1 : ℂ)) one_ne_zero
  | succ n ih =>
      have h := ih.mul hf
      have hfun : (fun x => f x ^ (n + 1)) = fun x => f x ^ n * f x := by
        funext x; rw [pow_succ]
      have hcoef : ((n : ℝ) * a + a) = ((n + 1 : ℕ) : ℝ) * a := by push_cast; ring
      rw [hfun, ← hcoef]
      exact h

/-! ## The Newton edge polynomial -/

/-- **An edge polynomial has a nonzero root.**  A complex polynomial carrying at least two nonzero
coefficients vanishes somewhere off the origin. -/
theorem exists_ne_zero_isRoot_of_one_lt_card_support {g : Polynomial ℂ}
    (h : 1 < g.support.card) : ∃ c : ℂ, c ≠ 0 ∧ g.IsRoot c := by
  classical
  have hg0 : g ≠ 0 := by
    intro hz
    rw [hz] at h
    simp at h
  obtain ⟨m, q, hq, hqne⟩ :
      ∃ (m : ℕ) (q : Polynomial ℂ), g = Polynomial.X ^ m * q ∧ q.coeff 0 ≠ 0 := by
    obtain ⟨q, hq⟩ : (Polynomial.X : Polynomial ℂ) ^ g.rootMultiplicity 0 ∣ g := by
      simpa using Polynomial.pow_rootMultiplicity_dvd g 0
    refine ⟨g.rootMultiplicity 0, q, hq, ?_⟩
    intro hz
    obtain ⟨r, hr⟩ := Polynomial.X_dvd_iff.mpr hz
    have hdvd : (Polynomial.X : Polynomial ℂ) ^ (g.rootMultiplicity 0 + 1) ∣ g := by
      refine ⟨r, ?_⟩
      calc g = Polynomial.X ^ g.rootMultiplicity 0 * q := hq
        _ = Polynomial.X ^ g.rootMultiplicity 0 * (Polynomial.X * r) := by rw [hr]
        _ = Polynomial.X ^ (g.rootMultiplicity 0 + 1) * r := by ring
    have hnot : ¬ ((Polynomial.X : Polynomial ℂ) ^ (g.rootMultiplicity 0 + 1) ∣ g) := by
      simpa using Polynomial.pow_rootMultiplicity_not_dvd hg0 (0 : ℂ)
    exact hnot hdvd
  have hqdeg : 1 ≤ q.natDegree := by
    by_contra hdeg
    have h0 : q.natDegree = 0 := by omega
    obtain ⟨a, rfl⟩ : ∃ a : ℂ, q = Polynomial.C a :=
      ⟨q.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero h0⟩
    have hgm : g = Polynomial.monomial m a := by
      rw [hq, mul_comm, Polynomial.C_mul_X_pow_eq_monomial]
    have hsupp : g.support ⊆ {m} := by
      rw [hgm]
      exact Polynomial.support_monomial_subset m a
    have hcard := Finset.card_le_card hsupp
    rw [Finset.card_singleton] at hcard
    omega
  obtain ⟨c, hc⟩ := Complex.exists_root (f := q)
    (by
      rw [Polynomial.degree_eq_natDegree (fun hz => by simp [hz] at hqdeg)]
      exact_mod_cast hqdeg)
  have hceval : q.eval c = 0 := hc
  refine ⟨c, ?_, ?_⟩
  · intro hzero
    rw [hzero] at hceval
    exact hqne (by rwa [Polynomial.coeff_zero_eq_eval_zero])
  · rw [Polynomial.IsRoot, hq, Polynomial.eval_mul, hceval, mul_zero]

/-- **A sum inherits its unique maximal weight.**  If one term's log-scale exponent strictly exceeds
every other, the sum has that exponent: the remaining terms are `o` of the dominant one, so the
correction factor tends to one and contributes nothing to the measured exponent. -/
theorem hasLogScaleExponent_sum_of_unique_max
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → α → ℂ) (w : ι → ℝ) (i₀ : ι)
    (hi₀ : i₀ ∈ s)
    (hg : ∀ i ∈ s, HasLogScaleExponent l ρ (g i) (w i))
    (hmax : ∀ i ∈ s, i ≠ i₀ → w i < w i₀) :
    HasLogScaleExponent l ρ (fun x => ∑ i ∈ s, g i x) (w i₀) := by
  have hg₀ := hg i₀ hi₀
  have hlogρ : Tendsto (fun x => Real.log (ρ x)) l atTop := Real.tendsto_log_atTop.comp hρ
  -- the other terms are negligible
  have hsmall : (fun x => ∑ i ∈ s.erase i₀, g i x) =o[l] g i₀ := by
    refine Asymptotics.IsLittleO.sum fun i hi => ?_
    exact isLittleO_of_hasLogScaleExponent_lt hρ (hg i (Finset.mem_of_mem_erase hi)) hg₀
      (hmax i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))
  have hR : Tendsto (fun x => (∑ i ∈ s.erase i₀, g i x) / g i₀ x) l (nhds 0) :=
    hsmall.tendsto_div_nhds_zero
  have hone : Tendsto (fun x => 1 + (∑ i ∈ s.erase i₀, g i x) / g i₀ x) l (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℂ)) (f := l)).add hR
  have hsplit : ∀ᶠ x in l,
      (∑ i ∈ s, g i x) = g i₀ x * (1 + (∑ i ∈ s.erase i₀, g i x) / g i₀ x) := by
    filter_upwards [hg₀.1] with x hx
    rw [mul_add, mul_one, mul_div_cancel₀ _ hx]
    exact (Finset.add_sum_erase s (fun i => g i x) hi₀).symm
  -- the correction factor is eventually a unit
  have hhalf : ∀ᶠ x in l, (1 : ℝ) / 2 < ‖1 + (∑ i ∈ s.erase i₀, g i x) / g i₀ x‖ := by
    have hcont : Tendsto (fun x => ‖1 + (∑ i ∈ s.erase i₀, g i x) / g i₀ x‖) l (nhds 1) := by
      simpa using hone.norm
    exact hcont.eventually_const_lt (by norm_num)
  refine ⟨?_, ?_⟩
  · filter_upwards [hsplit, hg₀.1, hhalf] with x hx hx0 hxh
    rw [hx]
    refine mul_ne_zero hx0 ?_
    intro hzero
    rw [hzero, norm_zero] at hxh
    linarith
  · have hlogfactor : Tendsto
        (fun x => Real.log ‖1 + (∑ i ∈ s.erase i₀, g i x) / g i₀ x‖ / Real.log (ρ x))
        l (nhds 0) := by
      have hlognorm : Tendsto
          (fun x => Real.log ‖1 + (∑ i ∈ s.erase i₀, g i x) / g i₀ x‖) l (nhds 0) := by
        have hnorm : Tendsto (fun x => ‖1 + (∑ i ∈ s.erase i₀, g i x) / g i₀ x‖) l (nhds 1) := by
          simpa using hone.norm
        simpa [Function.comp_def] using
          (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hnorm
      simpa using hlognorm.div_atTop hlogρ
    have hsum := hg₀.2.add hlogfactor
    rw [add_zero] at hsum
    refine Tendsto.congr' ?_ hsum
    filter_upwards [hsplit, hg₀.1, hhalf] with x hx hx0 hxh
    have hunit : (1 : ℂ) + (∑ i ∈ s.erase i₀, g i x) / g i₀ x ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hxh
      linarith
    rw [hx, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hx0) (norm_ne_zero_iff.mpr hunit), add_div]

/-- **A polynomial measures its own degree.**  Along a family whose log-scale exponent is one, a
nonzero polynomial evaluates to a quantity of log-scale exponent equal to its degree: the leading
monomial is the unique maximal weight. -/
theorem hasLogScaleExponent_polynomial_eval
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {u : α → ℂ} (hu : HasLogScaleExponent l ρ u 1) {q : Polynomial ℂ} (hq : q ≠ 0) :
    HasLogScaleExponent l ρ (fun x => q.eval (u x)) (q.natDegree : ℝ) := by
  classical
  have hsum : ∀ x : α, q.eval (u x) = ∑ k ∈ q.support, q.coeff k * (u x) ^ k := by
    intro x
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  have hmem : q.natDegree ∈ q.support :=
    Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hq)
  have hterm : ∀ k ∈ q.support,
      HasLogScaleExponent l ρ (fun x => q.coeff k * (u x) ^ k) ((k : ℝ)) := by
    intro k hk
    have hc : q.coeff k ≠ 0 := Polynomial.mem_support_iff.mp hk
    have h := (hasLogScaleExponent_const hρ hc).mul (hu.pow hρ k)
    have hval : (0 : ℝ) + (k : ℝ) * 1 = (k : ℝ) := by ring
    rwa [hval] at h
  have hmax : ∀ k ∈ q.support, k ≠ q.natDegree → (k : ℝ) < (q.natDegree : ℝ) := by
    intro k hk hne
    have hle : k ≤ q.natDegree := Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp hk)
    exact_mod_cast lt_of_le_of_ne hle hne
  have hres := hasLogScaleExponent_sum_of_unique_max hρ q.support
    (fun k x => q.coeff k * (u x) ^ k) (fun k => (k : ℝ)) q.natDegree hmem hterm hmax
  refine ⟨?_, ?_⟩
  · filter_upwards [hres.1] with x hx
    rw [hsum x]
    exact hx
  · refine Tendsto.congr' ?_ hres.2
    filter_upwards with x
    rw [hsum x]

/-- **The weight of a Newton monomial.**  A coefficient polynomial in the base variable times a
power of the measured ratio has weight `deg a + c p`. -/
theorem hasLogScaleExponent_newton_monomial
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {u T : α → ℂ} (hu : HasLogScaleExponent l ρ u 1) {p : ℝ}
    (hT : HasLogScaleExponent l ρ T p) {q : Polynomial ℂ} (hq : q ≠ 0) (c : ℕ) :
    HasLogScaleExponent l ρ (fun x => q.eval (u x) * (T x) ^ c)
      ((q.natDegree : ℝ) + (c : ℝ) * p) :=
  (hasLogScaleExponent_polynomial_eval hρ hu hq).mul (hT.pow hρ c)

/-- **The top symbol cannot vanish with a unique maximal weight.**  This is the Newton-edge step of
the Wiman reduction: along radii on which the ratio `f'/f` has measured exponent `p`, a top-symbol
relation `sum_i a_i(z) T^{c_i} = 0` forces the maximal weight `deg a_i + c_i p` to be attained at
least twice.  A single maximal monomial leaves a fixed positive weight gap, and the `o(1)` in each
measured exponent cannot close it. -/
theorem not_eventually_newton_sum_eq_zero_of_unique_max
    {α ι : Type*} {l : Filter α} [l.NeBot] {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {u T : α → ℂ} (hu : HasLogScaleExponent l ρ u 1) {p : ℝ}
    (hT : HasLogScaleExponent l ρ T p)
    (s : Finset ι) (q : ι → Polynomial ℂ) (c : ι → ℕ) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hq : ∀ i ∈ s, q i ≠ 0)
    (hmax : ∀ i ∈ s, i ≠ i₀ →
      ((q i).natDegree : ℝ) + (c i : ℝ) * p < ((q i₀).natDegree : ℝ) + (c i₀ : ℝ) * p) :
    ¬ (∀ᶠ x in l, ∑ i ∈ s, (q i).eval (u x) * (T x) ^ (c i) = 0) :=
  not_eventually_sum_eq_zero_of_unique_max hρ s
    (fun i => ((q i).natDegree : ℝ) + (c i : ℝ) * p)
    (fun i x => (q i).eval (u x) * (T x) ^ (c i))
    (fun i hi => hasLogScaleExponent_newton_monomial hρ hu hT (hq i hi) (c i)) hi₀ hmax

/-! ## Stability of the measured exponent -/

/-- The measured exponent only depends on the germ. -/
theorem HasLogScaleExponent.congr'
    {α : Type*} {l : Filter α} {ρ : α → ℝ} {f g : α → ℂ} {a : ℝ}
    (hf : HasLogScaleExponent l ρ f a) (hfg : ∀ᶠ x in l, f x = g x) :
    HasLogScaleExponent l ρ g a := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.1, hfg] with x hx heq using heq ▸ hx
  · refine Tendsto.congr' ?_ hf.2
    filter_upwards [hfg] with x heq
    rw [heq]

/-- **A factor tending to one does not move the exponent.**  The correction contributes
`log‖c‖ / log ρ`, which vanishes because the numerator tends to zero and the denominator to
infinity. -/
theorem HasLogScaleExponent.mul_tendsto_one
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {f c : α → ℂ} {a : ℝ} (hf : HasLogScaleExponent l ρ f a)
    (hc : Tendsto c l (nhds 1)) :
    HasLogScaleExponent l ρ (fun x => f x * c x) a := by
  have hlogρ : Tendsto (fun x => Real.log (ρ x)) l atTop := Real.tendsto_log_atTop.comp hρ
  have hnorm : Tendsto (fun x => ‖c x‖) l (nhds 1) := by simpa using hc.norm
  have hhalf : ∀ᶠ x in l, (1 : ℝ) / 2 < ‖c x‖ := hnorm.eventually_const_lt (by norm_num)
  have hcne : ∀ᶠ x in l, c x ≠ 0 := by
    filter_upwards [hhalf] with x hx
    intro hzero
    rw [hzero, norm_zero] at hx
    linarith
  have hlogc : Tendsto (fun x => Real.log ‖c x‖) l (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hnorm
  have hquot : Tendsto (fun x => Real.log ‖c x‖ / Real.log (ρ x)) l (nhds 0) := by
    simpa using hlogc.div_atTop hlogρ
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.1, hcne] with x hx hy using mul_ne_zero hx hy
  · have hsum := hf.2.add hquot
    rw [add_zero] at hsum
    refine Tendsto.congr' ?_ hsum
    filter_upwards [hf.1, hcne] with x hx hy
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy), add_div]

/-- **Asymptotically equal families measure the same exponent.**  If the ratio tends to one, the two
families have the same log-scale exponent.  This is what converts a Wiman--Valiron estimate
`z f'/f = nu (1 + o(1))` into the Newton-edge input for `f'/f`. -/
theorem HasLogScaleExponent.of_tendsto_ratio_one
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {f g : α → ℂ} {a : ℝ} (hf : HasLogScaleExponent l ρ f a)
    (hratio : Tendsto (fun x => g x / f x) l (nhds 1)) :
    HasLogScaleExponent l ρ g a := by
  refine (hf.mul_tendsto_one hρ hratio).congr' ?_
  filter_upwards [hf.1] with x hx
  rw [mul_div_cancel₀ _ hx]

/-- **A relative error tending to zero gives ratio one.**  If `A` differs from a positive real family
by at most `E`, and `E / nu` tends to zero, then `A / nu` tends to one. -/
theorem tendsto_ratio_one_of_norm_sub_le
    {α : Type*} {l : Filter α} {A : α → ℂ} {ν E : α → ℝ}
    (hν : ∀ᶠ x in l, 0 < ν x)
    (hbound : ∀ᶠ x in l, ‖A x - (ν x : ℂ)‖ ≤ E x)
    (hE : Tendsto (fun x => E x / ν x) l (nhds 0)) :
    Tendsto (fun x => A x / (ν x : ℂ)) l (nhds 1) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun x => dist_nonneg) ?_ hE
  filter_upwards [hν, hbound] with x hx hb
  have hxne : ((ν x : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hx
  have hsplit : A x / ((ν x : ℝ) : ℂ) - 1 = (A x - ((ν x : ℝ) : ℂ)) / ((ν x : ℝ) : ℂ) := by
    field_simp
  rw [Complex.dist_eq, hsplit, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  exact div_le_div_of_nonneg_right hb hx.le

/-- **The Wiman--Valiron estimate transfers the exponent.**  A family that agrees with the central
index up to a relative error tending to zero measures the same log-scale exponent.  This is the
statement that feeds the Newton-edge argument: the logarithmic derivative at the Wiman points has
the exponent of `nu(r)/z_r`. -/
theorem hasLogScaleExponent_of_relative_error
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {A : α → ℂ} {ν E : α → ℝ} {p : ℝ}
    (hνexp : HasLogScaleExponent l ρ (fun x => ((ν x : ℝ) : ℂ)) p)
    (hν : ∀ᶠ x in l, 0 < ν x)
    (hbound : ∀ᶠ x in l, ‖A x - (ν x : ℂ)‖ ≤ E x)
    (hE : Tendsto (fun x => E x / ν x) l (nhds 0)) :
    HasLogScaleExponent l ρ A p :=
  hνexp.of_tendsto_ratio_one hρ (tendsto_ratio_one_of_norm_sub_le hν hbound hE)

/-! ## Lower-degree terms vanish -/

/-- **A polynomially bounded numerator over a super-polynomial power vanishes.**  If `A` grows at
most like `r^N` and `V` outgrows `r^{N+1}`, then `A / V^j` tends to zero for every positive `j`.
This is the step that removes every term of total degree below the top one after an algebraic
differential equation is divided by a power of its transcendental entire solution. -/
theorem tendsto_div_pow_zero_of_dominates_pow
    {A V : ℝ → ℂ} {K : ℝ} {N j : ℕ} (hj : 0 < j) (hK : 0 ≤ K)
    (hA : ∀ᶠ r : ℝ in atTop, ‖A r‖ ≤ K * r ^ N)
    (hV : Tendsto (fun r : ℝ => ‖V r‖ / r ^ (N + 1)) atTop atTop) :
    Tendsto (fun r : ℝ => A r / (V r) ^ j) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hKr : Tendsto (fun r : ℝ => K / r) atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
  refine squeeze_zero' (Filter.Eventually.of_forall fun r => norm_nonneg _) ?_ hKr
  filter_upwards [hA, hV.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℝ)] with r hAr hVr hr1
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
  have hrN : (1 : ℝ) ≤ r ^ (N + 1) := one_le_pow₀ hr1
  have hrNpos : (0 : ℝ) < r ^ (N + 1) := by positivity
  have hVge : r ^ (N + 1) ≤ ‖V r‖ := by
    rw [le_div_iff₀ hrNpos] at hVr
    linarith
  have hV1 : (1 : ℝ) ≤ ‖V r‖ := le_trans hrN hVge
  have hVpos : (0 : ℝ) < ‖V r‖ := lt_of_lt_of_le one_pos hV1
  have hpowge : ‖V r‖ ≤ ‖V r‖ ^ j := le_self_pow₀ hV1 (by omega)
  have hnum : (0 : ℝ) ≤ K * r ^ N := by positivity
  rw [norm_div, norm_pow]
  calc ‖A r‖ / ‖V r‖ ^ j ≤ (K * r ^ N) / ‖V r‖ ^ j :=
        div_le_div_of_nonneg_right hAr (by positivity)
    _ ≤ (K * r ^ N) / ‖V r‖ := div_le_div_of_nonneg_left hnum hVpos hpowge
    _ ≤ (K * r ^ N) / r ^ (N + 1) := div_le_div_of_nonneg_left hnum hrNpos hVge
    _ = K / r := by
        rw [pow_succ]
        field_simp

/-- **A weight gap cannot be erased.**  A family of strictly larger measured exponent is never
`o` of one with a smaller exponent.  This is the `o`-form of the Newton-edge argument: the top symbol
is `o` of its own Newton scale, so its maximal weight cannot be attained by a single monomial. -/
theorem not_isLittleO_of_hasLogScaleExponent_lt
    {α : Type*} {l : Filter α} [l.NeBot] {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {f g : α → ℂ} {a b : ℝ} (hf : HasLogScaleExponent l ρ f a)
    (hg : HasLogScaleExponent l ρ g b) (hba : b < a) :
    ¬ (f =o[l] g) := by
  intro hlittle
  have hother : g =o[l] f := isLittleO_of_hasLogScaleExponent_lt hρ hg hf hba
  have h1 := hlittle.def (c := 1 / 2) (by norm_num)
  have h2 := hother.def (c := 1 / 2) (by norm_num)
  have hcontra : ∀ᶠ x in l, False := by
    filter_upwards [h1, h2, hf.1] with x hx hy hne
    have hpos : (0 : ℝ) < ‖f x‖ := norm_pos_iff.mpr hne
    linarith
  exact (Filter.eventually_false_iff_eq_bot.mp hcontra ▸ ‹l.NeBot›.ne) rfl

/-- **The Newton-edge conclusion in `o`-form.**  A top-symbol sum whose maximal weight is attained
by a single monomial cannot be `o` of any family of smaller measured exponent — in particular it is
not `o` of its own Newton scale. -/
theorem not_isLittleO_newton_sum_of_unique_max
    {α ι : Type*} {l : Filter α} [l.NeBot] {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {u T : α → ℂ} (hu : HasLogScaleExponent l ρ u 1) {p : ℝ}
    (hT : HasLogScaleExponent l ρ T p)
    (s : Finset ι) (q : ι → Polynomial ℂ) (c : ι → ℕ) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hq : ∀ i ∈ s, q i ≠ 0)
    (hmax : ∀ i ∈ s, i ≠ i₀ →
      ((q i).natDegree : ℝ) + (c i : ℝ) * p < ((q i₀).natDegree : ℝ) + (c i₀ : ℝ) * p)
    [DecidableEq ι] {g : α → ℂ} {b : ℝ} (hg : HasLogScaleExponent l ρ g b)
    (hba : b < ((q i₀).natDegree : ℝ) + (c i₀ : ℝ) * p) :
    ¬ ((fun x => ∑ i ∈ s, (q i).eval (u x) * (T x) ^ (c i)) =o[l] g) :=
  not_isLittleO_of_hasLogScaleExponent_lt hρ
    (hasLogScaleExponent_sum_of_unique_max hρ s
      (fun i x => (q i).eval (u x) * (T x) ^ (c i))
      (fun i => ((q i).natDegree : ℝ) + (c i : ℝ) * p) i₀ hi₀
      (fun i hi => hasLogScaleExponent_newton_monomial hρ hu hT (hq i hi) (c i)) hmax)
    hg hba

/-- **The base variable has exponent one.**  Measuring against the radius itself, the coordinate
`r` has log-scale exponent `1`.  This is the instantiation every application of the weight calculus
needs: the coefficient polynomials are evaluated at the base point. -/
theorem hasLogScaleExponent_coe_id :
    HasLogScaleExponent atTop (fun r : ℝ => r) (fun r : ℝ => (r : ℂ)) 1 := by
  constructor
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact_mod_cast ne_of_gt hr
  · refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop))
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
    have hrpos : (0 : ℝ) < r := lt_trans one_pos hr
    have hlog : Real.log r ≠ 0 := ne_of_gt (Real.log_pos hr)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    exact (div_self hlog).symm

/-- The measured exponent survives passage to a finer filter. -/
theorem HasLogScaleExponent.mono {α : Type*} {l l' : Filter α} {ρ : α → ℝ} {f : α → ℂ} {a : ℝ}
    (hf : HasLogScaleExponent l ρ f a) (h : l' ≤ l) :
    HasLogScaleExponent l' ρ f a :=
  ⟨hf.1.filter_mono h, hf.2.mono_left h⟩

/-- **Reduction I's Newton-edge conclusion, fully instantiated.**  Along any filter refining `atTop`
on which the ratio `T` has measured exponent `p`, a top-symbol relation in the base variable cannot
hold with a single maximal Newton weight. -/
theorem not_eventually_newton_sum_coe_eq_zero_of_unique_max
    {ι : Type*} {l : Filter ℝ} [l.NeBot] (hl : l ≤ atTop)
    {T : ℝ → ℂ} {p : ℝ} (hT : HasLogScaleExponent l (fun r : ℝ => r) T p)
    (s : Finset ι) (q : ι → Polynomial ℂ) (c : ι → ℕ) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hq : ∀ i ∈ s, q i ≠ 0)
    (hmax : ∀ i ∈ s, i ≠ i₀ →
      ((q i).natDegree : ℝ) + (c i : ℝ) * p < ((q i₀).natDegree : ℝ) + (c i₀ : ℝ) * p) :
    ¬ (∀ᶠ r : ℝ in l, ∑ i ∈ s, (q i).eval ((r : ℝ) : ℂ) * (T r) ^ (c i) = 0) :=
  not_eventually_newton_sum_eq_zero_of_unique_max (tendsto_id.mono_left hl)
    (hasLogScaleExponent_coe_id.mono hl) hT s q c hi₀ hq hmax

/-! ## The edge polynomial -/

/-- The coefficient of the edge polynomial at an exponent occurring on the face. -/
private theorem edge_coeff_eq {ι : Type*} [DecidableEq ι] (face : Finset ι)
    (q : ι → Polynomial ℂ) (c : ι → ℕ) (hinj : Set.InjOn c face) {j : ι} (hj : j ∈ face) :
    (∑ i ∈ face, Polynomial.C (q i).leadingCoeff * Polynomial.X ^ (c i)).coeff (c j)
      = (q j).leadingCoeff := by
  classical
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_single_of_mem j hj ?_ |>.trans ?_
  · intro i hi hij
    have hne : c i ≠ c j := fun h => hij (hinj hi hj h)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne.symm, mul_zero]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp

/-- **The Newton edge has a nonzero root.**  If the maximal face carries at least two distinct
exponents, its edge polynomial has two nonzero coefficients, hence a root off the origin.  This is
the last step of Reduction I: the slope `p` is realised by an actual branch. -/
theorem exists_ne_zero_isRoot_edge {ι : Type*} [DecidableEq ι] (face : Finset ι)
    (q : ι → Polynomial ℂ) (c : ι → ℕ) (hq : ∀ i ∈ face, q i ≠ 0)
    (hinj : Set.InjOn c face) {i₁ i₂ : ι} (h1 : i₁ ∈ face) (h2 : i₂ ∈ face) (hne : i₁ ≠ i₂) :
    ∃ z : ℂ, z ≠ 0 ∧
      (∑ i ∈ face, Polynomial.C (q i).leadingCoeff * Polynomial.X ^ (c i)).IsRoot z := by
  classical
  set E : Polynomial ℂ := ∑ i ∈ face, Polynomial.C (q i).leadingCoeff * Polynomial.X ^ (c i) with hE
  have hmem : ∀ j ∈ face, c j ∈ E.support := by
    intro j hj
    rw [Polynomial.mem_support_iff, hE, edge_coeff_eq face q c hinj hj]
    exact Polynomial.leadingCoeff_ne_zero.mpr (hq j hj)
  have hcne : c i₁ ≠ c i₂ := fun h => hne (hinj h1 h2 h)
  have hcard : 1 < E.support.card := by
    have hsub : ({c i₁, c i₂} : Finset ℕ) ⊆ E.support := by
      intro k hk
      rcases Finset.mem_insert.mp hk with hk | hk
      · rw [hk]; exact hmem i₁ h1
      · rw [Finset.mem_singleton.mp hk]; exact hmem i₂ h2
    have hpair : ({c i₁, c i₂} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hcne), Finset.card_singleton]
    calc 1 < 2 := by norm_num
      _ = ({c i₁, c i₂} : Finset ℕ).card := hpair.symm
      _ ≤ E.support.card := Finset.card_le_card hsub
  obtain ⟨z, hz0, hzroot⟩ := exists_ne_zero_isRoot_of_one_lt_card_support hcard
  exact ⟨z, hz0, hzroot⟩

end GaloisForLFunctions.HTGeometry
