import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation

/-!
# The order-two shift-orbit mass obstruction

A shift difference `y(z + H) - y(z)` of a function with finitely many poles has zero total
order-two principal-part mass along every `Hℤ`-orbit: the orbit coefficients telescope.  A sum of
inverse squares has strictly negative total order-two mass on any orbit meeting its pole set, so no
such sum is a shift difference.

This is the obstruction that forces the logarithmic derivative of a finite product of Gamma factors
with commensurable positive scales to be hypertranscendental.  Translation by the common step turns
the product into a rational multiple of itself, so the second logarithmic derivative satisfies

`τ(z + H) - τ(z) = -∑ (z + β)⁻²`,

with one inverse square for every pole of the shift multiplier, all with the same sign.  The theorem
below says this equation has no rational — indeed no finitely-poled meromorphic — solution.

The telescoping happens separately at each Laurent index, so no bound on the pole order of a
hypothetical solution is needed.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-! ### Telescoping over an integer interval -/

/-- Telescoping a forward difference over an integer interval. -/
theorem sum_Ico_sub_telescope (d : ℤ → ℂ) (l : ℤ) :
    ∀ u : ℤ, l ≤ u → ∑ n ∈ Finset.Ico l u, (d (n + 1) - d n) = d u - d l := by
  intro u hu
  induction u, hu using Int.leInduction with
  | base => simp
  | succ k hk ih =>
      have hins : Finset.Ico l (k + 1) = insert k (Finset.Ico l k) := by
        ext n
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      rw [hins, Finset.sum_insert (by simp), ih]
      ring

/-- A finitely supported integer family is supported in a symmetric interval. -/
theorem exists_symmetric_support_bound {d : ℤ → ℂ} (hd : {n : ℤ | d n ≠ 0}.Finite) :
    ∃ N : ℕ, ∀ n : ℤ, d n ≠ 0 → -(N : ℤ) < n ∧ n < (N : ℤ) := by
  classical
  obtain ⟨t, ht⟩ := hd.exists_finset
  refine ⟨(t.image fun n => n.natAbs).sup id + 1, fun n hn => ?_⟩
  have hmem : n ∈ t := (ht n).mpr hn
  have hle : n.natAbs ≤ (t.image fun n => n.natAbs).sup id :=
    Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hmem)
  constructor <;> [skip; skip] <;> · push_cast; omega

/-! ### The cofinite filter refines every punctured neighbourhood -/

/-- On the plane, a property holding off a finite set holds near every point. -/
theorem nhdsNE_le_cofinite (a : ℂ) : 𝓝[≠] a ≤ (Filter.cofinite : Filter ℂ) := by
  intro S hS
  rw [Filter.mem_cofinite] at hS
  have hclosed : IsClosed (Sᶜ \ {a}) := (hS.sdiff).isClosed
  refine mem_nhdsWithin.mpr ⟨(Sᶜ \ {a})ᶜ, hclosed.isOpen_compl, by simp, ?_⟩
  rintro z ⟨hz, hzne⟩
  by_contra hzS
  exact hz ⟨hzS, hzne⟩

/-! ### The telescoping identity for the orbit coefficients -/

/-- **Zero orbit mass of a shift difference.**  If the Laurent coefficients of `y` at index `ℓ`
vanish outside a symmetric window along the orbit `a + Hℤ`, the coefficients of `z ↦ y (z + H) - y z`
sum to zero over that window. -/
theorem sum_Ico_laurentCoeff_shiftDiff_eq_zero {y : ℂ → ℂ} (hy : MeromorphicOn y Set.univ)
    {H a : ℂ} {ℓ : ℤ} {N : ℕ}
    (hout : ∀ n : ℤ, (n ≤ -(N : ℤ) ∨ (N : ℤ) ≤ n) → laurentCoeff y (a + (n : ℂ) * H) ℓ = 0) :
    ∑ n ∈ Finset.Ico (-(N : ℤ)) (N : ℤ),
        laurentCoeff (fun z => y (z + H) - y z) (a + (n : ℂ) * H) ℓ = 0 := by
  set d : ℤ → ℂ := fun n => laurentCoeff y (a + (n : ℂ) * H) ℓ with hd
  have hstep : ∀ n : ℤ,
      laurentCoeff (fun z => y (z + H) - y z) (a + (n : ℂ) * H) ℓ = d (n + 1) - d n := by
    intro n
    rw [laurentCoeff_shiftDiff hy H (a + (n : ℂ) * H) ℓ]
    have hpt : a + (n : ℂ) * H + H = a + ((n + 1 : ℤ) : ℂ) * H := by push_cast; ring
    rw [hpt]
  have h1 : d (N : ℤ) = 0 := hout (N : ℤ) (Or.inr le_rfl)
  have h2 : d (-(N : ℤ)) = 0 := hout (-(N : ℤ)) (Or.inl le_rfl)
  rw [Finset.sum_congr rfl fun n _ => hstep n,
    sum_Ico_sub_telescope d (-(N : ℤ)) (N : ℤ) (by omega), h1, h2, sub_zero]

/-! ### The order-two coefficient of an inverse square -/

/-- The cube clearing shift of an inverse square at its own pole is the identity. -/
theorem laurentShift_invSq_self (p : ℂ) :
    laurentShift (fun z => ((z - p) ^ (2 : ℕ))⁻¹) p 3 = fun t : ℂ => t := by
  funext t
  simp only [laurentShift, add_sub_cancel_left]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · field_simp

/-- The order-two coefficient of an inverse square at its pole is one. -/
theorem laurentCoeff_invSq_self (p : ℂ) :
    laurentCoeff (fun z => ((z - p) ^ (2 : ℕ))⁻¹) p (-2) = 1 := by
  have hana : AnalyticAt ℂ (laurentShift (fun z => ((z - p) ^ (2 : ℕ))⁻¹) p 3) 0 := by
    rw [laurentShift_invSq_self]
    exact analyticAt_id
  rw [laurentCoeff_eq_taylorCoeffZero hana (by norm_num), laurentShift_invSq_self]
  norm_num [taylorCoeffZero, iteratedDeriv_one]

theorem analyticAt_invSq {p q : ℂ} (h : q ≠ p) : AnalyticAt ℂ (fun z => ((z - p) ^ (2 : ℕ))⁻¹) q := by
  have h1 : AnalyticAt ℂ (fun z : ℂ => (z - p) ^ (2 : ℕ)) q := (analyticAt_id.sub analyticAt_const).pow 2
  exact h1.inv (pow_ne_zero 2 (sub_ne_zero.mpr h))

theorem meromorphicAt_invSq (p q : ℂ) : MeromorphicAt (fun z => ((z - p) ^ (2 : ℕ))⁻¹) q := by
  have h1 : MeromorphicAt (fun z : ℂ => (z - p) ^ (2 : ℕ)) q :=
    ((analyticAt_id.sub analyticAt_const).pow 2).meromorphicAt
  exact h1.inv

/-- The order-two coefficient of an inverse square away from its pole vanishes. -/
theorem laurentCoeff_invSq_of_ne {p q : ℂ} (h : q ≠ p) :
    laurentCoeff (fun z => ((z - p) ^ (2 : ℕ))⁻¹) q (-2) = 0 :=
  laurentCoeff_eq_zero_of_analyticAt (analyticAt_invSq h) (by norm_num)

/-- **The order-two mass of a negative sum of inverse squares.**  It counts, with a minus sign, the
inverse squares whose pole sits at the evaluation point. -/
theorem laurentCoeff_negSumInvSq {ι : Type*} (s : Finset ι) (p : ι → ℂ) (q : ℂ) :
    laurentCoeff (fun z => -∑ i ∈ s, ((z - p i) ^ (2 : ℕ))⁻¹) q (-2)
      = -((s.filter fun i => p i = q).card : ℂ) := by
  classical
  have hrw : (fun z : ℂ => -∑ i ∈ s, ((z - p i) ^ (2 : ℕ))⁻¹)
      = fun z : ℂ => ∑ i ∈ s, (-1 : ℂ) * ((z - p i) ^ (2 : ℕ))⁻¹ := by
    funext z
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hrw, laurentCoeff_sum s (fun i z => ((z - p i) ^ (2 : ℕ))⁻¹) (fun _ => (-1 : ℂ)) q (-2)
    (fun i _ => meromorphicAt_invSq (p i) q)]
  have hterm : ∀ i ∈ s, (-1 : ℂ) * laurentCoeff (fun z => ((z - p i) ^ (2 : ℕ))⁻¹) q (-2)
      = if p i = q then (-1 : ℂ) else 0 := by
    intro i _
    rcases eq_or_ne (p i) q with hpi | hpi
    · subst hpi
      rw [laurentCoeff_invSq_self, if_pos rfl, mul_one]
    · rw [laurentCoeff_invSq_of_ne (Ne.symm hpi), if_neg hpi, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, mul_neg_one]

/-! ### The obstruction -/

/-- **The shift-orbit mass obstruction, one orbit at a time.**  If the poles of a sum of inverse
squares meet the orbit `a + Hℤ`, that sum is not the shift difference of any meromorphic function
with finitely many poles.

The order-two Laurent coefficients of a shift difference telescope along the orbit, hence sum to
zero, while the coefficients of the inverse-square sum are all `≤ 0` with at least one nonzero. -/
theorem not_shiftDifference_negSumInvSq_orbit {H a : ℂ} (hH : H ≠ 0) {ι : Type*} (s : Finset ι)
    (p : ι → ℂ) (s₀ : Finset ι) (hsub : s₀ ⊆ s) (ν : ι → ℤ)
    (hp : ∀ i ∈ s₀, p i = a + (ν i : ℂ) * H)
    (hoff : ∀ i ∈ s, i ∉ s₀ → ∀ n : ℤ, p i ≠ a + (n : ℂ) * H) (hs : s₀.Nonempty)
    {y : ℂ → ℂ} (hy : MeromorphicOn y Set.univ)
    (hpoles : {z : ℂ | ¬ AnalyticAt ℂ y z}.Finite) :
    ¬ ((fun z => y (z + H) - y z)
        =ᶠ[Filter.cofinite] fun z => -∑ i ∈ s, ((z - p i) ^ (2 : ℕ))⁻¹) := by
  classical
  intro heq
  -- the orbit points are pairwise distinct
  have hinj : Function.Injective fun n : ℤ => a + (n : ℂ) * H := by
    intro m n hmn
    have : (m : ℂ) * H = (n : ℂ) * H := by linear_combination hmn
    have hcast : (m : ℂ) = (n : ℂ) := mul_right_cancel₀ hH this
    exact_mod_cast hcast
  -- the order-two coefficients of `y` along the orbit have finite support
  set d : ℤ → ℂ := fun n => laurentCoeff y (a + (n : ℂ) * H) (-2) with hd
  have hsupp : {n : ℤ | d n ≠ 0}.Finite := by
    refine Set.Finite.subset (Set.Finite.preimage (f := fun n : ℤ => a + (n : ℂ) * H)
      (hinj.injOn) hpoles) ?_
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    intro hana
    exact hn (laurentCoeff_eq_zero_of_analyticAt hana (by norm_num))
  obtain ⟨N₁, hN₁⟩ := exists_symmetric_support_bound hsupp
  -- a window containing every orbit index of the poles
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ i ∈ s₀, -(N₂ : ℤ) ≤ ν i ∧ ν i < (N₂ : ℤ) := by
    refine ⟨(s₀.image fun i => (ν i).natAbs).sup id + 1, fun i hi => ?_⟩
    have hle : (ν i).natAbs ≤ (s₀.image fun i => (ν i).natAbs).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hi)
    constructor <;> [skip; skip] <;> · push_cast; omega
  set N : ℕ := max N₁ N₂ with hN
  have hout : ∀ n : ℤ, (n ≤ -(N : ℤ) ∨ (N : ℤ) ≤ n) → d n = 0 := by
    intro n hn
    by_contra hne
    obtain ⟨h1, h2⟩ := hN₁ n hne
    have : (N₁ : ℤ) ≤ (N : ℤ) := by exact_mod_cast le_max_left N₁ N₂
    omega
  -- the two evaluations of the same sum
  have hzero := sum_Ico_laurentCoeff_shiftDiff_eq_zero (y := y) hy (H := H) (a := a) (ℓ := -2)
    (N := N) hout
  have hterm : ∀ n : ℤ,
      laurentCoeff (fun z => y (z + H) - y z) (a + (n : ℂ) * H) (-2)
        = -((s.filter fun i => p i = a + (n : ℂ) * H).card : ℂ) := by
    intro n
    have hmero : MeromorphicAt (fun z => y (z + H) - y z) (a + (n : ℂ) * H) :=
      (meromorphicAt_comp_add.mpr (hy _ (Set.mem_univ _))).sub (hy _ (Set.mem_univ _))
    rw [laurentCoeff_congr hmero (heq.filter_mono (nhdsNE_le_cofinite _)) (-2),
      laurentCoeff_negSumInvSq]
  rw [Finset.sum_congr rfl fun n _ => hterm n] at hzero
  -- the total mass counts the poles
  have hmaps : Set.MapsTo ν ↑s₀ ↑(Finset.Ico (-(N : ℤ)) (N : ℤ)) := by
    intro i hi
    have hi' : i ∈ s₀ := hi
    obtain ⟨h1, h2⟩ := hN₂ i hi'
    have : (N₂ : ℤ) ≤ (N : ℤ) := by exact_mod_cast le_max_right N₁ N₂
    simp only [Finset.coe_Ico, Set.mem_Ico]
    omega
  have hfiber : ∀ n ∈ Finset.Ico (-(N : ℤ)) (N : ℤ),
      (s.filter fun i => p i = a + (n : ℂ) * H) = s₀.filter fun i => ν i = n := by
    intro n _
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨his, hpi⟩
      have hi₀ : i ∈ s₀ := by
        by_contra hcon
        exact hoff i his hcon n hpi
      refine ⟨hi₀, hinj ?_⟩
      show a + ((ν i : ℤ) : ℂ) * H = a + (n : ℂ) * H
      rw [← hp i hi₀, hpi]
    · rintro ⟨hi₀, hν⟩
      exact ⟨hsub hi₀, by rw [hp i hi₀, hν]⟩
  have hcount : s₀.card = ∑ n ∈ Finset.Ico (-(N : ℤ)) (N : ℤ),
      (s.filter fun i => p i = a + (n : ℂ) * H).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    exact Finset.sum_congr rfl fun n hn => by rw [hfiber n hn]
  have hsum : ∑ n ∈ Finset.Ico (-(N : ℤ)) (N : ℤ),
      -((s.filter fun i => p i = a + (n : ℂ) * H).card : ℂ) = -(s₀.card : ℂ) := by
    rw [Finset.sum_neg_distrib]
    congr 1
    rw [hcount, Nat.cast_sum]
  rw [hsum, neg_eq_zero] at hzero
  have : s₀.card = 0 := by exact_mod_cast hzero
  exact absurd (Finset.card_eq_zero.mp this) hs.ne_empty

/-- **The shift-orbit mass obstruction.**  A nonempty sum of inverse squares is never a shift
difference of a meromorphic function with finitely many poles.

Any pole of the sum determines an orbit; the poles lying on it contribute the whole order-two mass
there, and it is nonzero. -/
theorem not_shiftDifference_negSumInvSq {H : ℂ} (hH : H ≠ 0) {ι : Type*} (s : Finset ι)
    (p : ι → ℂ) (hs : s.Nonempty) {y : ℂ → ℂ} (hy : MeromorphicOn y Set.univ)
    (hpoles : {z : ℂ | ¬ AnalyticAt ℂ y z}.Finite) :
    ¬ ((fun z => y (z + H) - y z)
        =ᶠ[Filter.cofinite] fun z => -∑ i ∈ s, ((z - p i) ^ (2 : ℕ))⁻¹) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hs
  set a : ℂ := p i₀ with ha
  set s₀ : Finset ι := s.filter (fun i => ∃ n : ℤ, p i = a + (n : ℂ) * H) with hs₀
  have hmem : ∀ i, i ∈ s₀ ↔ i ∈ s ∧ ∃ n : ℤ, p i = a + (n : ℂ) * H := by
    intro i
    rw [hs₀, Finset.mem_filter]
  set ν : ι → ℤ := fun i =>
    if h : ∃ n : ℤ, p i = a + (n : ℂ) * H then h.choose else 0 with hν
  have hp : ∀ i ∈ s₀, p i = a + (ν i : ℂ) * H := by
    intro i hi
    obtain ⟨-, hex⟩ := (hmem i).mp hi
    rw [hν]
    simp only [dif_pos hex]
    exact hex.choose_spec
  have hoff : ∀ i ∈ s, i ∉ s₀ → ∀ n : ℤ, p i ≠ a + (n : ℂ) * H := by
    intro i his hni n hpi
    exact hni ((hmem i).mpr ⟨his, ⟨n, hpi⟩⟩)
  have hs₀ne : s₀.Nonempty := ⟨i₀, (hmem i₀).mpr ⟨hi₀, ⟨0, by rw [ha]; ring⟩⟩⟩
  exact not_shiftDifference_negSumInvSq_orbit hH s p s₀ (Finset.filter_subset _ _) ν hp hoff
    hs₀ne hy hpoles

/-- **No rational solution of the archimedean shift equation.**  The rational form of the
obstruction: `y(z + H) - y(z) = -∑ (z - p i)⁻²` has no solution in rational functions. -/
theorem not_rational_shiftDifference_negSumInvSq {H : ℂ} (hH : H ≠ 0) {ι : Type*} (s : Finset ι)
    (p : ι → ℂ) (hs : s.Nonempty) (P Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    ¬ ((fun z => Polynomial.eval (z + H) P / Polynomial.eval (z + H) Q
          - Polynomial.eval z P / Polynomial.eval z Q)
        =ᶠ[Filter.cofinite] fun z => -∑ i ∈ s, ((z - p i) ^ (2 : ℕ))⁻¹) := by
  classical
  have hPana : ∀ z : ℂ, AnalyticAt ℂ (fun w => Polynomial.eval w P) z := by
    intro z
    exact (Polynomial.differentiable_aeval P).differentiableOn.analyticAt Filter.univ_mem
  have hQana : ∀ z : ℂ, AnalyticAt ℂ (fun w => Polynomial.eval w Q) z := by
    intro z
    exact (Polynomial.differentiable_aeval Q).differentiableOn.analyticAt Filter.univ_mem
  set y : ℂ → ℂ := fun z => Polynomial.eval z P / Polynomial.eval z Q with hy
  have hymero : MeromorphicOn y Set.univ := by
    intro z _
    exact (hPana z).meromorphicAt.div (hQana z).meromorphicAt
  have hpoles : {z : ℂ | ¬ AnalyticAt ℂ y z}.Finite := by
    refine Set.Finite.subset (Polynomial.finite_setOf_isRoot hQ) ?_
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    by_contra hroot
    exact hz ((hPana z).div (hQana z) hroot)
  exact not_shiftDifference_negSumInvSq hH s p hs hymero hpoles


/-! ### The second logarithmic derivative of a product of linear factors -/

/-- Away from its roots, the logarithmic derivative of a finite product of linear factors is the
sum of the reciprocals of the factors. -/
theorem logDeriv_prod_sub {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) {w : ℂ}
    (h : ∀ i ∈ s, w ≠ ρ i) :
    logDeriv (fun u => ∏ i ∈ s, (u - ρ i)) w = ∑ i ∈ s, (w - ρ i)⁻¹ := by
  rw [logDeriv_prod (fun i hi => sub_ne_zero.mpr (h i hi)) (fun i _ => by fun_prop)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hd : HasDerivAt (fun u : ℂ => u - ρ i) 1 w := (hasDerivAt_id w).sub_const (ρ i)
  rw [logDeriv_apply, hd.deriv, one_div]

/-- The derivative of a finite sum of reciprocals of linear factors. -/
theorem deriv_sum_inv_sub {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) {z : ℂ}
    (h : ∀ i ∈ s, z ≠ ρ i) :
    deriv (fun w => ∑ i ∈ s, (w - ρ i)⁻¹) z = -∑ i ∈ s, ((z - ρ i) ^ (2 : ℕ))⁻¹ := by
  have hterm : ∀ i ∈ s, HasDerivAt (fun w : ℂ => (w - ρ i)⁻¹) (-((z - ρ i) ^ (2 : ℕ))⁻¹) z := by
    intro i hi
    have hd : HasDerivAt (fun u : ℂ => u - ρ i) 1 z := (hasDerivAt_id z).sub_const (ρ i)
    have hinv := hd.inv (sub_ne_zero.mpr (h i hi))
    have hrw : -(1 : ℂ) / (z - ρ i) ^ (2 : ℕ) = -((z - ρ i) ^ (2 : ℕ))⁻¹ := by
      rw [neg_div, one_div]
    rw [hrw] at hinv
    exact hinv
  have hsum : HasDerivAt (fun w : ℂ => ∑ i ∈ s, (w - ρ i)⁻¹)
      (∑ i ∈ s, -((z - ρ i) ^ (2 : ℕ))⁻¹) z := HasDerivAt.fun_sum hterm
  rw [hsum.deriv, Finset.sum_neg_distrib]

/-- **The second logarithmic derivative of a product of linear factors.**  Off the roots it is the
negative sum of the inverse squares of the factors. -/
theorem deriv_logDeriv_prod_sub {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) {z : ℂ}
    (h : ∀ i ∈ s, z ≠ ρ i) :
    deriv (logDeriv fun u => ∏ i ∈ s, (u - ρ i)) z = -∑ i ∈ s, ((z - ρ i) ^ (2 : ℕ))⁻¹ := by
  classical
  have hopen : IsOpen {w : ℂ | ∀ i ∈ s, w ≠ ρ i} := by
    have hcompl : {w : ℂ | ∀ i ∈ s, w ≠ ρ i} = (↑(s.image ρ) : Set ℂ)ᶜ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Finset.mem_coe]
      constructor
      · intro hw hmemT
        obtain ⟨i, hi, hEq⟩ := Finset.mem_image.mp hmemT
        exact hw i hi hEq.symm
      · intro hw i hi hEq
        exact hw (by rw [hEq]; exact Finset.mem_image_of_mem ρ hi)
    rw [hcompl]
    exact (s.image ρ).finite_toSet.isClosed.isOpen_compl
  have hev : (logDeriv fun u => ∏ i ∈ s, (u - ρ i)) =ᶠ[nhds z] fun w => ∑ i ∈ s, (w - ρ i)⁻¹ := by
    filter_upwards [hopen.mem_nhds h] with w hw
    exact logDeriv_prod_sub s ρ hw
  rw [hev.deriv_eq, deriv_sum_inv_sub s ρ h]

/-- **The archimedean shift obstruction.**  The second logarithmic derivative of a nonempty product
of linear factors is not the shift difference of any meromorphic function with finitely many poles.

This is the rational shift equation of a finite Gamma product with commensurable positive scales:
translating by the common period multiplies the product by such a polynomial, so its second
logarithmic derivative would have to be the shift difference of the second logarithmic derivative of
the product itself. -/
theorem not_shiftDifference_deriv_logDeriv_prod_sub {H : ℂ} (hH : H ≠ 0) {ι : Type*} (s : Finset ι)
    (ρ : ι → ℂ) (hs : s.Nonempty) {y : ℂ → ℂ} (hy : MeromorphicOn y Set.univ)
    (hpoles : {z : ℂ | ¬ AnalyticAt ℂ y z}.Finite) :
    ¬ ((fun z => y (z + H) - y z)
        =ᶠ[Filter.cofinite] fun z => deriv (logDeriv fun u => ∏ i ∈ s, (u - ρ i)) z) := by
  classical
  intro heq
  refine not_shiftDifference_negSumInvSq hH s ρ hs hy hpoles (heq.trans ?_)
  have hfin : (↑(s.image ρ) : Set ℂ).Finite := (s.image ρ).finite_toSet
  rw [Filter.EventuallyEq, Filter.eventually_cofinite]
  refine hfin.subset fun z hz => ?_
  simp only [Set.mem_setOf_eq] at hz
  by_contra hnot
  refine hz (deriv_logDeriv_prod_sub s ρ fun i hi hzi => hnot ?_)
  rw [hzi]
  exact Finset.mem_coe.mpr (Finset.mem_image_of_mem ρ hi)


/-- A product of affine factors has the logarithmic derivative of the monic product of the same
roots: the leading constant cancels. -/
theorem logDeriv_prod_affine_eq {ι : Type*} (s : Finset ι) (α β : ι → ℂ)
    (hα : ∀ i ∈ s, α i ≠ 0) :
    (logDeriv fun u => ∏ i ∈ s, (α i * u + β i))
      = logDeriv fun u => ∏ i ∈ s, (u - -(β i) / α i) := by
  have hfun : (fun u : ℂ => ∏ i ∈ s, (α i * u + β i))
      = fun u : ℂ => (∏ i ∈ s, α i) * ∏ i ∈ s, (u - -(β i) / α i) := by
    funext u
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hne : α i ≠ 0 := hα i hi
    field_simp
    ring
  funext w
  rw [hfun, logDeriv_const_mul w _ (Finset.prod_ne_zero_iff.mpr hα)]

/-- **The rational shift equation of a finite Gamma product has no finitely-poled solution.**
Translating a product `exp (a z) ∏ Γ (λ i z + μ i)` with commensurable positive scales by the common
period multiplies it by a constant times `∏ (λ i z + μ i + ℓ)`, so its second logarithmic derivative
`τ` would satisfy `τ (z + H) - τ z = (P'/P)' (z)` for that product of affine factors.  No function
with finitely many poles satisfies this. -/
theorem not_shiftDifference_deriv_logDeriv_prod_affine {H : ℂ} (hH : H ≠ 0) {ι : Type*}
    (s : Finset ι) (α β : ι → ℂ) (hα : ∀ i ∈ s, α i ≠ 0) (hs : s.Nonempty)
    {y : ℂ → ℂ} (hy : MeromorphicOn y Set.univ)
    (hpoles : {z : ℂ | ¬ AnalyticAt ℂ y z}.Finite) :
    ¬ ((fun z => y (z + H) - y z)
        =ᶠ[Filter.cofinite] fun z => deriv (logDeriv fun u => ∏ i ∈ s, (α i * u + β i)) z) := by
  rw [logDeriv_prod_affine_eq s α β hα]
  exact not_shiftDifference_deriv_logDeriv_prod_sub hH s (fun i => -(β i) / α i) hs hy hpoles

end GaloisForLFunctions.HTGeometry
