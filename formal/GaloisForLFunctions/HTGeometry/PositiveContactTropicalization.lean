import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Positive analytic contact tropicalization

Exact local factorization package for finite-order real-analytic contacts at the origin.  It records
the first Taylor order and leading coefficient, proves positivity forces even order and positive
leading coefficient, and establishes the tropical sum, product, observation, and ramified pullback
laws without cancellation hypotheses hidden in the statements.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Exact analytic contact data at the origin.  `leading` is the first Taylor coefficient: the
analytic unit in `f(x) = x^order * unit(x)` takes this value at zero. -/
def AnalyticContact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (order : ℕ) (leading : E) : Prop :=
  ∃ unit : ℝ → E, AnalyticAt ℝ unit 0 ∧ unit 0 = leading ∧ leading ≠ 0 ∧
    ∀ᶠ x in 𝓝 0, f x = x ^ order • unit x

/-- Positive scalar contact: exact analytic contact with positive leading Taylor coefficient. -/
def PositiveAnalyticContact (f : ℝ → ℝ) (order : ℕ) (leading : ℝ) : Prop :=
  AnalyticContact f order leading ∧ (∀ᶠ x in 𝓝 0, 0 ≤ f x) ∧ 0 < leading

namespace AnalyticContact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f g : ℝ → E} {m n : ℕ} {a b : E}

theorem analyticAt (h : AnalyticContact f m a) : AnalyticAt ℝ f 0 := by
  rcases h with ⟨u, hu, _hu0, _ha, hfactor⟩
  have hmodel : AnalyticAt ℝ (fun x : ℝ => x ^ m • u x) 0 :=
    (analyticAt_id.pow m).smul hu
  exact hmodel.congr (EventuallyEq.symm hfactor)

theorem analyticOrderAt_eq (h : AnalyticContact f m a) : analyticOrderAt f 0 = m := by
  rcases h with ⟨u, hu, hu0, ha, hfactor⟩
  apply (analyticAt ⟨u, hu, hu0, ha, hfactor⟩).analyticOrderAt_eq_natCast.mpr
  refine ⟨u, hu, ?_, ?_⟩
  · simpa [hu0] using ha
  · simpa using hfactor

/-- A contact whose value vanishes at the origin has strictly positive order. -/
theorem order_pos_of_value_zero (h : AnalyticContact f m a) (hzero : f 0 = 0) : 0 < m := by
  by_contra hnot
  have hm : m = 0 := Nat.eq_zero_of_not_pos hnot
  rcases h with ⟨u, hu, hu0, ha, hfactor⟩
  have hfa : f 0 = a := by
    have h := hfactor.self_of_nhds
    simpa [hm, hu0] using h
  exact ha (hfa.symm.trans hzero)

theorem leading_eq_of_eventuallyEq (hf : AnalyticContact f m a)
    (hg : AnalyticContact g m b) (hfg : f =ᶠ[𝓝 0] g) : a = b := by
  rcases hf with ⟨uf, huf, huf0, ha, hffactor⟩
  rcases hg with ⟨ug, hug, hug0, hb, hgfactor⟩
  have hunit : uf =ᶠ[𝓝[≠] 0] ug := by
    filter_upwards [self_mem_nhdsWithin,
      hffactor.filter_mono nhdsWithin_le_nhds,
      hgfactor.filter_mono nhdsWithin_le_nhds,
      hfg.filter_mono nhdsWithin_le_nhds] with x hx hfx hgx heq
    apply smul_right_injective E (pow_ne_zero m hx)
    exact hfx.symm.trans (heq.trans hgx)
  have hf_tendsto : Tendsto uf (𝓝[≠] 0) (𝓝 a) := by
    simpa [huf0] using huf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hg_tendsto : Tendsto ug (𝓝[≠] 0) (𝓝 b) := by
    simpa [hug0] using hug.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique (hf_tendsto.congr' hunit) hg_tendsto

theorem leading_eq (hf : AnalyticContact f m a) (hg : AnalyticContact f m b) : a = b :=
  hf.leading_eq_of_eventuallyEq hg (Eventually.of_forall fun _ => rfl)

theorem neg (h : AnalyticContact f m a) :
    AnalyticContact (fun x => -f x) m (-a) := by
  rcases h with ⟨u, hu, hu0, ha, hfactor⟩
  refine ⟨fun x => -u x, hu.neg, by simp [hu0], neg_ne_zero.mpr ha, ?_⟩
  filter_upwards [hfactor] with x hx
  rw [hx]
  simp

/-- Exact ramification law for analytic contact. -/
theorem comp {phi : ℝ → ℝ} {r : ℕ} {c : ℝ} (hf : AnalyticContact f m a)
    (hphi : AnalyticContact phi r c) (hr : 0 < r) :
    AnalyticContact (fun x => f (phi x)) (r * m) (c ^ m • a) := by
  rcases hf with ⟨uf, huf, huf0, ha, hffactor⟩
  rcases hphi with ⟨uphi, huphi, huphi0, hc, hphifactor⟩
  have hphi0 : phi 0 = 0 := by
    have h := hphifactor.self_of_nhds
    simpa [Nat.ne_of_gt hr] using h
  have hphi_analytic : AnalyticAt ℝ phi 0 :=
    AnalyticContact.analyticAt ⟨uphi, huphi, huphi0, hc, hphifactor⟩
  have hphi_tendsto : Tendsto phi (𝓝 0) (𝓝 0) := by
    have hc' : Tendsto phi (𝓝 0) (𝓝 (phi 0)) := hphi_analytic.continuousAt
    simpa [hphi0] using hc'
  have huf_comp : AnalyticAt ℝ (fun x => uf (phi x)) 0 := by
    have huf_at : AnalyticAt ℝ uf (phi 0) := by simpa [hphi0] using huf
    simpa [Function.comp_def] using huf_at.comp hphi_analytic
  refine ⟨fun x => uphi x ^ m • uf (phi x),
    (huphi.pow m).smul huf_comp, ?_, ?_, ?_⟩
  · simp [huphi0, hphi0, huf0]
  · exact smul_ne_zero (pow_ne_zero m hc) ha
  · filter_upwards [hphifactor, hphi_tendsto.eventually hffactor] with x hpx hfx
    change phi x = x ^ r * uphi x at hpx
    rw [hfx, hpx]
    rw [mul_pow, ← pow_mul]
    simp [smul_smul]

/-- Negating the parameter is an exact simple contact. -/
theorem negId : AnalyticContact (fun x : ℝ => -x) 1 (-1 : ℝ) := by
  refine ⟨fun _ => (-1 : ℝ), analyticAt_const, rfl, by norm_num, ?_⟩
  filter_upwards with x
  simp

/-- Local odd reflection forces odd ramification order. -/
theorem order_odd_of_antireflection {phi : ℝ → ℝ} {r : ℕ} {c : ℝ}
    (hphi : AnalyticContact phi r c) (_hr : 0 < r)
    (hreflect : ∀ᶠ x in 𝓝 0, phi (-x) = -phi x) : Odd r := by
  have hcomp := hphi.comp negId (by norm_num)
  have hneg := hphi.neg
  have hcomp' : AnalyticContact (fun x => phi (-x)) r ((-1 : ℝ) ^ r • c) := by
    simpa using hcomp
  have hlead : (-1 : ℝ) ^ r * c = -c := by
    simpa [smul_eq_mul] using hcomp'.leading_eq_of_eventuallyEq hneg hreflect
  have hc : c ≠ 0 := by
    rcases hphi with ⟨_u, _hu, _hu0, hc, _hfactor⟩
    exact hc
  have hpow : (-1 : ℝ) ^ r = -1 := by
    apply mul_right_cancel₀ hc
    simpa using hlead
  rcases Nat.even_or_odd r with heven | hodd
  · rw [heven.neg_one_pow] at hpow
    norm_num at hpow
  · exact hodd

end AnalyticContact

namespace PositiveAnalyticContact

variable {f g : ℝ → ℝ} {m n : ℕ} {a b : ℝ}

theorem analyticAt (h : PositiveAnalyticContact f m a) : AnalyticAt ℝ f 0 :=
  h.1.analyticAt

theorem analyticOrderAt_eq (h : PositiveAnalyticContact f m a) : analyticOrderAt f 0 = m :=
  h.1.analyticOrderAt_eq

private theorem exists_right_of_eventually_nhds {p : ℝ → Prop} (hp : ∀ᶠ x in 𝓝 0, p x) :
    ∃ x, 0 < x ∧ p x := by
  rcases Metric.eventually_nhds_iff.mp hp with ⟨ε, hε, hball⟩
  refine ⟨ε / 2, half_pos hε, hball ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
  linarith

private theorem exists_left_of_eventually_nhds {p : ℝ → Prop} (hp : ∀ᶠ x in 𝓝 0, p x) :
    ∃ x, x < 0 ∧ p x := by
  rcases Metric.eventually_nhds_iff.mp hp with ⟨ε, hε, hball⟩
  refine ⟨-(ε / 2), neg_lt_zero.mpr (half_pos hε), hball ?_⟩
  rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hε)]
  linarith

/-- A finite-order analytic germ nonnegative on a full neighborhood has exact positive contact
data at its analytic order. -/
theorem exists_of_analytic_eventually_nonnegative
    (hf : AnalyticAt ℝ f 0) (hfinite : analyticOrderAt f 0 ≠ ⊤)
    (hnonneg : ∀ᶠ x in 𝓝 0, 0 ≤ f x) :
    ∃ a, PositiveAnalyticContact f (analyticOrderAt f 0).toNat a := by
  let m := (analyticOrderAt f 0).toNat
  have horder : analyticOrderAt f 0 = (m : ℕ∞) := (ENat.coe_toNat hfinite).symm
  obtain ⟨u, hu, hu0, hfactor⟩ := hf.analyticOrderAt_eq_natCast.mp horder
  have hu0pos : 0 < u 0 := by
    rcases lt_or_gt_of_ne hu0 with hu0neg | hu0pos
    · have huneg : ∀ᶠ x in 𝓝 0, u x < 0 :=
        hu.continuousAt.eventually_lt_const hu0neg
      obtain ⟨x, hxpos, hx⟩ := exists_right_of_eventually_nhds
        (hnonneg.and (hfactor.and huneg))
      have hxpow : 0 < x ^ m := pow_pos hxpos m
      have : f x < 0 := by
        rw [hx.2.1]
        simpa [smul_eq_mul] using mul_neg_of_pos_of_neg hxpow hx.2.2
      linarith
    · exact hu0pos
  refine ⟨u 0, ?_, hnonneg, hu0pos⟩
  exact ⟨u, hu, rfl, ne_of_gt hu0pos, by simpa [smul_eq_mul] using hfactor⟩

/-- Exact extraction for the positive zero-germ class `A₊`: contact data exists and its order is
strictly positive. -/
theorem exists_of_analytic_zero_eventually_nonnegative
    (hf : AnalyticAt ℝ f 0) (hzero : f 0 = 0)
    (hfinite : analyticOrderAt f 0 ≠ ⊤) (hnonneg : ∀ᶠ x in 𝓝 0, 0 ≤ f x) :
    ∃ a, PositiveAnalyticContact f (analyticOrderAt f 0).toNat a ∧
      0 < (analyticOrderAt f 0).toNat := by
  obtain ⟨a, ha⟩ := exists_of_analytic_eventually_nonnegative hf hfinite hnonneg
  exact ⟨a, ha, ha.1.order_pos_of_value_zero hzero⟩

/-- Two-sided nonnegativity forces even contact order. -/
theorem order_even (h : PositiveAnalyticContact f m a) : Even m := by
  rcases h.1 with ⟨u, hu, hu0, ha, hfactor⟩
  rcases Nat.even_or_odd m with heven | hodd
  · exact heven
  · have hupos : ∀ᶠ x in 𝓝 0, 0 < u x := by
      have hcont : Tendsto u (𝓝 0) (𝓝 (u 0)) := hu.continuousAt
      rw [hu0] at hcont
      exact hcont.eventually_const_lt h.2.2
    obtain ⟨x, hxneg, hx⟩ := exists_left_of_eventually_nhds
      (h.2.1.and (hfactor.and hupos))
    have hxpow : x ^ m < 0 := Odd.pow_neg hodd hxneg
    have : f x < 0 := by
      rw [hx.2.1]
      simpa [smul_eq_mul] using mul_neg_of_neg_of_pos hxpow hx.2.2
    linarith

/-- If first contact of `f` occurs strictly before first contact of `g`, positive addition retains
the order and leading coefficient of `f`. -/
theorem add_of_lt (hf : PositiveAnalyticContact f m a)
    (hg : PositiveAnalyticContact g n b) (hmn : m < n) :
    PositiveAnalyticContact (fun x => f x + g x) m a := by
  rcases hf.1 with ⟨uf, huf, huf0, ha, hffactor⟩
  rcases hg.1 with ⟨ug, hug, hug0, hb, hgfactor⟩
  have hdiff : 0 < n - m := Nat.sub_pos_of_lt hmn
  refine ⟨?_, ?_, hf.2.2⟩
  · refine ⟨fun x => uf x + x ^ (n - m) * ug x,
      huf.add ((analyticAt_id.pow (n - m)).mul hug), ?_, ha, ?_⟩
    · change uf 0 + 0 ^ (n - m) * ug 0 = a
      rw [zero_pow (Nat.ne_of_gt hdiff), zero_mul, add_zero, huf0]
    · filter_upwards [hffactor, hgfactor] with x hfx hgx
      simp only [smul_eq_mul] at hfx hgx ⊢
      rw [hfx, hgx, mul_add]
      have hpow : x ^ n = x ^ m * x ^ (n - m) := by
        rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hmn)]
      rw [hpow]
      ring
  · filter_upwards [hf.2.1, hg.2.1] with x hfx hgx
    linarith

/-- Equal positive contacts add their leading Taylor coefficients without cancellation. -/
theorem add_of_eq (hf : PositiveAnalyticContact f m a)
    (hg : PositiveAnalyticContact g m b) :
    PositiveAnalyticContact (fun x => f x + g x) m (a + b) := by
  rcases hf.1 with ⟨uf, huf, huf0, ha, hffactor⟩
  rcases hg.1 with ⟨ug, hug, hug0, hb, hgfactor⟩
  refine ⟨?_, ?_, add_pos hf.2.2 hg.2.2⟩
  · refine ⟨fun x => uf x + ug x, huf.add hug, by simp [huf0, hug0],
      ne_of_gt (add_pos hf.2.2 hg.2.2), ?_⟩
    filter_upwards [hffactor, hgfactor] with x hfx hgx
    simp only [smul_eq_mul] at hfx hgx ⊢
    rw [hfx, hgx, mul_add]
  · filter_upwards [hf.2.1, hg.2.1] with x hfx hgx
    linarith

/-- Symmetric strict-order branch of positive addition. -/
theorem add_of_gt (hf : PositiveAnalyticContact f m a)
    (hg : PositiveAnalyticContact g n b) (hnm : n < m) :
    PositiveAnalyticContact (fun x => f x + g x) n b := by
  simpa [add_comm] using hg.add_of_lt hf hnm

/-- Tropical addition law, including exact surviving leading coefficient. -/
theorem exists_add_min (hf : PositiveAnalyticContact f m a)
    (hg : PositiveAnalyticContact g n b) :
    ∃ c, PositiveAnalyticContact (fun x => f x + g x) (min m n) c := by
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · exact ⟨a, by simpa [min_eq_left (Nat.le_of_lt hmn)] using hf.add_of_lt hg hmn⟩
  · subst n
    exact ⟨a + b, by simpa using hf.add_of_eq hg⟩
  · exact ⟨b, by simpa [min_eq_right (Nat.le_of_lt hnm)] using hf.add_of_gt hg hnm⟩

/-- Tropical order law for positive addition. -/
theorem analyticOrderAt_add_eq_min (hf : PositiveAnalyticContact f m a)
    (hg : PositiveAnalyticContact g n b) :
    analyticOrderAt (fun x => f x + g x) 0 = min m n := by
  obtain ⟨c, hc⟩ := hf.exists_add_min hg
  exact hc.analyticOrderAt_eq

/-- Product contacts add orders and multiply leading Taylor coefficients. -/
theorem mul (hf : PositiveAnalyticContact f m a)
    (hg : PositiveAnalyticContact g n b) :
    PositiveAnalyticContact (fun x => f x * g x) (m + n) (a * b) := by
  rcases hf.1 with ⟨uf, huf, huf0, ha, hffactor⟩
  rcases hg.1 with ⟨ug, hug, hug0, hb, hgfactor⟩
  refine ⟨?_, ?_, mul_pos hf.2.2 hg.2.2⟩
  · refine ⟨fun x => uf x * ug x, huf.mul hug, by simp [huf0, hug0],
      mul_ne_zero ha hb, ?_⟩
    filter_upwards [hffactor, hgfactor] with x hfx hgx
    simp only [smul_eq_mul] at hfx hgx ⊢
    rw [hfx, hgx, pow_add]
    ring
  · filter_upwards [hf.2.1, hg.2.1] with x hfx hgx
    positivity

/-- Observation inequality: `0 ≤ g ≤ f` near the contact point forces the observed germ `g` to
vanish to at least the order of `f`. -/
theorem order_le_of_eventually_le (hf : PositiveAnalyticContact f m a)
    (hg : PositiveAnalyticContact g n b)
    (hle : ∀ᶠ x in 𝓝 0, g x ≤ f x) : m ≤ n := by
  let d : ℝ → ℝ := fun x => f x - g x
  have hd_analytic : AnalyticAt ℝ d 0 := hf.analyticAt.sub hg.analyticAt
  have hd_nonneg : ∀ᶠ x in 𝓝 0, 0 ≤ d x := by
    filter_upwards [hle] with x hx
    dsimp [d]
    linarith
  by_cases hdtop : analyticOrderAt d 0 = ⊤
  · have hd_zero : ∀ᶠ x in 𝓝 0, d x = 0 := analyticOrderAt_eq_top.mp hdtop
    have hfg : f =ᶠ[𝓝 0] g := by
      filter_upwards [hd_zero] with x hx
      dsimp [d] at hx
      linarith
    have hord := analyticOrderAt_congr hfg
    rw [hf.analyticOrderAt_eq, hg.analyticOrderAt_eq] at hord
    exact Nat.le_of_eq (ENat.coe_inj.mp hord)
  · obtain ⟨c, hc⟩ := exists_of_analytic_eventually_nonnegative hd_analytic hdtop hd_nonneg
    obtain ⟨q, hsum⟩ := hg.exists_add_min hc
    have hsum_eq : (fun x => g x + d x) =ᶠ[𝓝 0] f :=
      Eventually.of_forall fun x => by simp [d]
    have hord := analyticOrderAt_congr hsum_eq
    rw [hsum.analyticOrderAt_eq, hf.analyticOrderAt_eq] at hord
    have hnat : min n (analyticOrderAt d 0).toNat = m := ENat.coe_inj.mp hord
    omega

/-- At equal order, the observation inequality also compares exact leading Taylor coefficients. -/
theorem leading_le_of_eventually_le_of_order_eq (hf : PositiveAnalyticContact f m a)
    (hg : PositiveAnalyticContact g n b)
    (hle : ∀ᶠ x in 𝓝 0, g x ≤ f x) (hmn : m = n) : b ≤ a := by
  subst n
  let d : ℝ → ℝ := fun x => f x - g x
  have hd_analytic : AnalyticAt ℝ d 0 := hf.analyticAt.sub hg.analyticAt
  have hd_nonneg : ∀ᶠ x in 𝓝 0, 0 ≤ d x := by
    filter_upwards [hle] with x hx
    dsimp [d]
    linarith
  have hsum_eq : (fun x => g x + d x) =ᶠ[𝓝 0] f :=
    Eventually.of_forall fun x => by simp [d]
  by_cases hdtop : analyticOrderAt d 0 = ⊤
  · have hd_zero : ∀ᶠ x in 𝓝 0, d x = 0 := analyticOrderAt_eq_top.mp hdtop
    have hfg : f =ᶠ[𝓝 0] g := by
      filter_upwards [hd_zero] with x hx
      dsimp [d] at hx
      linarith
    exact le_of_eq (hg.1.leading_eq_of_eventuallyEq hf.1 hfg.symm)
  · obtain ⟨c, hc⟩ := exists_of_analytic_eventually_nonnegative hd_analytic hdtop hd_nonneg
    let k := (analyticOrderAt d 0).toNat
    rcases lt_trichotomy m k with hmk | hmk | hkm
    · have hcontact := hg.add_of_lt hc hmk
      have hab : b = a := hcontact.1.leading_eq_of_eventuallyEq hf.1 hsum_eq
      exact hab.le
    · subst k
      have hk : (analyticOrderAt d 0).toNat = m := hmk.symm
      have hc' : PositiveAnalyticContact d m c := hk ▸ hc
      have hcontact := hg.add_of_eq hc'
      have hab : b + c = a := hcontact.1.leading_eq_of_eventuallyEq hf.1 hsum_eq
      linarith [hc.2.2]
    · have hcontact := hc.add_of_lt hg hkm
      have hcontact' : PositiveAnalyticContact (fun x => g x + d x) k c := by
        simpa [k, add_comm] using hcontact
      have hord := analyticOrderAt_congr hsum_eq
      rw [hcontact'.analyticOrderAt_eq, hf.analyticOrderAt_eq] at hord
      have : k = m := ENat.coe_inj.mp hord
      omega

/-- A nonempty finite positive sum has contact order equal to the minimum constituent order. -/
theorem exists_finset_sum_min {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (F : ι → ℝ → ℝ) (order : ι → ℕ)
    (leading : ι → ℝ)
    (hcontact : ∀ i ∈ s, PositiveAnalyticContact (F i) (order i) (leading i)) :
    ∃ c, PositiveAnalyticContact (fun x => ∑ i ∈ s, F i x) (s.inf' hs order) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert i s hi ih =>
      by_cases hs0 : s.Nonempty
      · obtain ⟨c, hc⟩ := ih hs0 (fun j hj => hcontact j (Finset.mem_insert_of_mem hj))
        obtain ⟨q, hq⟩ := (hcontact i (Finset.mem_insert_self i s)).exists_add_min hc
        refine ⟨q, ?_⟩
        have hinf : (insert i s).inf' hs order = min (order i) (s.inf' hs0 order) := by
          rw [Finset.inf'_insert hs0]
        rw [hinf]
        simpa [Finset.sum_insert hi] using hq
      · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs0
        subst s
        refine ⟨leading i, ?_⟩
        simpa using hcontact i (Finset.mem_singleton_self i)

/-- Exact recovery: equality of analytic germs preserves both contact order and leading
coefficient. -/
theorem order_leading_eq_of_eventuallyEq (hf : PositiveAnalyticContact f m a)
    (hg : PositiveAnalyticContact g n b) (hfg : f =ᶠ[𝓝 0] g) : m = n ∧ a = b := by
  have hord := analyticOrderAt_congr hfg
  rw [hf.analyticOrderAt_eq, hg.analyticOrderAt_eq] at hord
  have hmn : m = n := ENat.coe_inj.mp hord
  subst n
  exact ⟨rfl, hf.1.leading_eq_of_eventuallyEq hg.1 hfg⟩

/-- `N` identical positive copies preserve order and multiply leading coefficient by `N`. -/
theorem natCopies (hf : PositiveAnalyticContact f m a) {N : ℕ} (hN : 0 < N) :
    PositiveAnalyticContact (fun x => (N : ℝ) * f x) m ((N : ℝ) * a) := by
  rcases hf.1 with ⟨u, hu, hu0, ha, hfactor⟩
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨?_, ?_, mul_pos hNreal hf.2.2⟩
  · refine ⟨fun x => (N : ℝ) * u x, (analyticAt_const.mul hu), by simp [hu0],
      mul_ne_zero (ne_of_gt hNreal) ha, ?_⟩
    filter_upwards [hfactor] with x hx
    simp only [smul_eq_mul] at hx ⊢
    rw [hx]
    ring
  · filter_upwards [hf.2.1] with x hx
    positivity

end PositiveAnalyticContact

/-! ### Finite-dimensional Gram contacts -/

/-- Real inner product as a continuous bilinear map, represented in the analytic API as a
two-variable continuous multilinear map. -/
def realInnerContinuousMultilinearMap {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
  ContinuousMultilinearMap.mk
    { toFun := fun v => inner ℝ (v 0) (v 1)
      map_update_add' := by
        intro _inst v i x y
        fin_cases i <;> simp [inner_add_left, inner_add_right]
      map_update_smul' := by
        intro _inst v i c x
        fin_cases i <;> simp [real_inner_smul_left, real_inner_smul_right] }
    (by
      have hpair : Continuous (fun v : Fin 2 → E => (v 0, v 1)) :=
        (continuous_apply 0).prodMk (continuous_apply 1)
      have hi : Continuous (fun p : E × E => inner ℝ p.1 p.2) :=
        (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := E)).continuous
      simpa [Function.comp_def] using hi.comp hpair)

/-- Inner products of real-analytic vector germs are real analytic. -/
theorem analyticAt_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v w : ℝ → E} (hv : AnalyticAt ℝ v 0) (hw : AnalyticAt ℝ w 0) :
    AnalyticAt ℝ (fun x => inner ℝ (v x) (w x)) 0 := by
  let pair : ℝ → (Fin 2 → E) := fun x i => if i = 0 then v x else w x
  have hpair : AnalyticAt ℝ pair 0 := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    · simpa [pair] using hv
    · simpa [pair] using hw
  have hinner := (realInnerContinuousMultilinearMap (E := E)).analyticAt.comp hpair
  refine hinner.congr (Eventually.of_forall ?_)
  intro x
  change inner ℝ (pair x 0) (pair x 1) = inner ℝ (v x) (w x)
  simp [pair]

/-- Exact Gram law: squared norm doubles vector contact order and squares leading norm. -/
theorem positiveAnalyticContact_normSq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v : ℝ → E} {m : ℕ} {a : E}
    (hv : AnalyticContact v m a) :
    PositiveAnalyticContact (fun x => ‖v x‖ ^ 2) (2 * m) (‖a‖ ^ 2) := by
  rcases hv with ⟨u, hu, hu0, ha, hvfactor⟩
  have hunit_analytic : AnalyticAt ℝ (fun x => inner ℝ (u x) (u x)) 0 :=
    analyticAt_inner hu hu
  have hlead : 0 < ‖a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr ha)
  refine ⟨?_, Eventually.of_forall (fun x => sq_nonneg ‖v x‖), hlead⟩
  refine ⟨fun x => inner ℝ (u x) (u x), hunit_analytic, ?_, ne_of_gt hlead, ?_⟩
  · simp [hu0]
  · filter_upwards [hvfactor] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
    have hpow : x ^ (2 * m) = (x ^ m) * (x ^ m) := by
      rw [Nat.mul_comm 2 m, pow_mul, pow_two]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hpow]
    change (x ^ m) ^ 2 * ‖u x‖ ^ 2 = (x ^ m * x ^ m) * ‖u x‖ ^ 2
    rw [pow_two]

/-- Finite positive Gram sums tropicalize to minimum doubled vector order. -/
theorem exists_positiveAnalyticContact_finset_sum_normSq {ι E : Type*}
    [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset ι) (hs : s.Nonempty) (v : ι → ℝ → E) (order : ι → ℕ)
    (leading : ι → E) (hcontact : ∀ i ∈ s, AnalyticContact (v i) (order i) (leading i)) :
    ∃ c, PositiveAnalyticContact (fun x => ∑ i ∈ s, ‖v i x‖ ^ 2)
      (2 * s.inf' hs order) c := by
  obtain ⟨c, hc⟩ := PositiveAnalyticContact.exists_finset_sum_min s hs
    (fun i x => ‖v i x‖ ^ 2) (fun i => 2 * order i) (fun i => ‖leading i‖ ^ 2)
    (fun i hi => positiveAnalyticContact_normSq (hcontact i hi))
  have hinf : s.inf' hs (fun i => 2 * order i) = 2 * s.inf' hs order := by
    apply le_antisymm
    · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_inf' hs order
      calc
        s.inf' hs (fun j => 2 * order j) ≤ 2 * order i := Finset.inf'_le _ hi
        _ = 2 * s.inf' hs order := by rw [heq]
    · apply Finset.le_inf' hs
      intro i hi
      exact Nat.mul_le_mul_left 2 (Finset.inf'_le order hi)
  exact ⟨c, hinf ▸ hc⟩

/-! ### Ramification ledger -/

/-- Contact order multiplies exactly under a positive-order analytic ramification. -/
theorem analyticOrderAt_comp_eq_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {phi : ℝ → ℝ} {m r : ℕ} {a : E} {b : ℝ}
    (hf : AnalyticContact f m a) (hphi : AnalyticContact phi r b) (hr : 0 < r) :
    analyticOrderAt (fun x => f (phi x)) 0 = r * m :=
  (hf.comp hphi hr).analyticOrderAt_eq

/-- Multiplication by an odd ramification index preserves parity. -/
theorem even_mul_iff_of_odd_left {r k : ℕ} (hr : Odd r) : Even (r * k) ↔ Even k := by
  constructor
  · intro hrk
    rcases Nat.even_or_odd k with hk | hk
    · exact hk
    · exact False.elim ((Nat.not_even_iff_odd.mpr (hr.mul hk)) hrk)
  · intro hk
    exact hk.mul_left r

/-- Reflection-compatible ramification preserves parity of every half-order. -/
theorem halfOrder_parity_iff_of_antireflection {phi : ℝ → ℝ} {r k : ℕ} {b : ℝ}
    (hphi : AnalyticContact phi r b) (hr : 0 < r)
    (hreflect : ∀ᶠ x in 𝓝 0, phi (-x) = -phi x) :
    Even (r * k) ↔ Even k :=
  even_mul_iff_of_odd_left (hphi.order_odd_of_antireflection hr hreflect)

end

end GaloisForLFunctions.HTGeometry
