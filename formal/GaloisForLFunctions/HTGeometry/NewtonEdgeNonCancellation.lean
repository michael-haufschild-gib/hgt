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

end GaloisForLFunctions.HTGeometry
