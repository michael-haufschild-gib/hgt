import GaloisForLFunctions.RHTower.Sieve.ShortIntervalThetaEveryWindow
import GaloisForLFunctions.HTGeometry.WindowAssignmentStep

/-!
# The Rayleigh floor of a prime window

The primes of a short window `(x, x + x^θ]`, weighted by `log p` and rescaled to `[0,1]`, carry a
moment matrix with a quantitative positive-definiteness floor.  The floor comes from the
unconditional short-interval prime mass on every subwindow together with the block Rayleigh bound:
each of `J` separated subwindows carries mass `≫ x^θ / J`, and a polynomial with unit coefficient
norm cannot be small on all of them.
-/

noncomputable section

open MeasureTheory Set Finset

namespace RHTower.Sieve

/-- The Chebyshev increment counts exactly the primes of the window. -/
theorem theta_sub_eq_sum_Ioc {u v : ℝ} (huv : u ≤ v) :
    Chebyshev.theta v - Chebyshev.theta u
      = ∑ p ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊ with Nat.Prime p, Real.log p := by
  classical
  have hfl : ⌊u⌋₊ ≤ ⌊v⌋₊ := Nat.floor_le_floor huv
  have hsplit := Finset.sum_Ioc_consecutive
    (fun p : ℕ => if Nat.Prime p then Real.log p else 0) (Nat.zero_le ⌊u⌋₊) hfl
  have hcast : ∀ S : Finset ℕ,
      (∑ p ∈ S, if Nat.Prime p then Real.log p else 0) = ∑ p ∈ S with Nat.Prime p, Real.log p := by
    intro S
    rw [Finset.sum_filter]
  rw [hcast, hcast, hcast] at hsplit
  rw [Chebyshev.theta, Chebyshev.theta, ← hsplit]
  ring

/-- The primes of a window, as a `Finset`. -/
def windowPrimes (x y : ℝ) : Finset ℕ :=
  {p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ | Nat.Prime p}

theorem mem_windowPrimes {x y : ℝ} {p : ℕ} :
    p ∈ windowPrimes x y ↔ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ ∧ Nat.Prime p := by
  rw [windowPrimes, Finset.mem_filter]

/-- The window primes indexed by `Fin (card)`. -/
def windowPrimeIndex (x y : ℝ) : Fin (windowPrimes x y).card → ℕ :=
  fun r => ((windowPrimes x y).equivFin.symm r : ℕ)

theorem windowPrimeIndex_mem (x y : ℝ) (r : Fin (windowPrimes x y).card) :
    windowPrimeIndex x y r ∈ windowPrimes x y :=
  ((windowPrimes x y).equivFin.symm r).2

theorem windowPrimeIndex_injective (x y : ℝ) : Function.Injective (windowPrimeIndex x y) := by
  intro r r' h
  have h' : (windowPrimes x y).equivFin.symm r = (windowPrimes x y).equivFin.symm r' :=
    Subtype.ext h
  exact (windowPrimes x y).equivFin.symm.injective h'

theorem windowPrimeIndex_prime (x y : ℝ) (r : Fin (windowPrimes x y).card) :
    Nat.Prime (windowPrimeIndex x y r) :=
  (mem_windowPrimes.1 (windowPrimeIndex_mem x y r)).2

/-- The indexed family enumerates the window primes. -/
theorem image_windowPrimeIndex (x y : ℝ) :
    Finset.univ.image (windowPrimeIndex x y) = windowPrimes x y := by
  classical
  ext q
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, rfl⟩
    exact windowPrimeIndex_mem x y r
  · intro hq
    refine ⟨(windowPrimes x y).equivFin ⟨q, hq⟩, ?_⟩
    rw [windowPrimeIndex, Equiv.symm_apply_apply]

/-- Summing a function over the indexed family is summing it over the window primes. -/
theorem sum_windowPrimeIndex (x y : ℝ) (f : ℕ → ℝ) (T : Finset ℕ) :
    (∑ r ∈ Finset.univ with windowPrimeIndex x y r ∈ T, f (windowPrimeIndex x y r))
      = ∑ q ∈ windowPrimes x y with q ∈ T, f q := by
  classical
  have hkey := Finset.sum_image
    (s := {r ∈ Finset.univ | windowPrimeIndex x y r ∈ T})
    (g := windowPrimeIndex x y) (f := f)
    (fun r _ r' _ h => windowPrimeIndex_injective x y h)
  rw [← hkey, ← Finset.filter_image (f := windowPrimeIndex x y) (s := Finset.univ)
    (p := fun q => q ∈ T), image_windowPrimeIndex]

/-- The weighted mass of a block of window primes is a Chebyshev increment. -/
theorem sum_log_windowPrimeIndex_block {x y u v : ℝ} (huv : u ≤ v) (hxu : x ≤ u) (hvy : v ≤ y) :
    (∑ r ∈ Finset.univ with windowPrimeIndex x y r ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊,
        Real.log (windowPrimeIndex x y r))
      = Chebyshev.theta v - Chebyshev.theta u := by
  classical
  rw [sum_windowPrimeIndex x y (fun q => Real.log q) (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊),
    theta_sub_eq_sum_Ioc huv]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext q
  simp only [Finset.mem_filter, mem_windowPrimes, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨_, hprime⟩, hq⟩
    exact ⟨hq, hprime⟩
  · rintro ⟨hq, hprime⟩
    refine ⟨⟨⟨?_, ?_⟩, hprime⟩, hq⟩
    · exact lt_of_le_of_lt (Nat.floor_le_floor hxu) hq.1
    · exact le_trans hq.2 (Nat.floor_le_floor hvy)

/-- The lower edge of the `i`-th prime subwindow, as a fraction of the window length. -/
def subwindowLeft (J : ℕ) (i : Fin J) : ℝ := (2 * (i : ℕ) : ℝ) / (2 * J)

/-- The upper edge of the `i`-th prime subwindow. -/
def subwindowRight (J : ℕ) (i : Fin J) : ℝ := (2 * (i : ℕ) + 1 : ℝ) / (2 * J)

theorem subwindowLeft_nonneg {J : ℕ} (i : Fin J) : 0 ≤ subwindowLeft J i := by
  rw [subwindowLeft]
  positivity

theorem subwindowLeft_lt_right {J : ℕ} (hJ : 0 < J) (i : Fin J) :
    subwindowLeft J i < subwindowRight J i := by
  have hJ0 : (0:ℝ) < 2 * J := by
    have : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
    linarith
  rw [subwindowLeft, subwindowRight, div_lt_div_iff_of_pos_right hJ0]
  linarith

theorem subwindowRight_le_one {J : ℕ} (hJ : 0 < J) (i : Fin J) : subwindowRight J i ≤ 1 := by
  have hJ0 : (0:ℝ) < 2 * J := by
    have : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
    linarith
  rw [subwindowRight, div_le_one hJ0]
  have hi : ((i : ℕ) : ℝ) + 1 ≤ (J : ℝ) := by
    have := i.2
    exact_mod_cast Nat.succ_le_of_lt this
  linarith

theorem subwindowRight_sub_left {J : ℕ} (i : Fin J) :
    subwindowRight J i - subwindowLeft J i = 1 / (2 * J) := by
  rw [subwindowRight, subwindowLeft, div_sub_div_same]
  ring_nf

/-- Separated subwindows: distinct blocks are `1/(2J)` apart. -/
theorem subwindow_separated {J : ℕ} (hJ : 0 < J) {i k : Fin J} (hik : i ≠ k)
    {s u : ℝ} (hs : s ∈ Set.Icc (subwindowLeft J i) (subwindowRight J i))
    (hu : u ∈ Set.Icc (subwindowLeft J k) (subwindowRight J k)) :
    1 / (2 * J) ≤ |s - u| := by
  have hJ0 : (0:ℝ) < 2 * J := by
    have : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
    linarith
  have hpos : (0:ℝ) < 1 / (2 * (J : ℝ)) := by positivity
  rcases lt_or_gt_of_ne (fun h : (i : ℕ) = (k : ℕ) => hik (Fin.ext h)) with h | h
  · have hik1 : ((i : ℕ) : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    have h1 : s ≤ (2 * (i : ℕ) + 1 : ℝ) / (2 * J) := hs.2
    have h2 : (2 * (k : ℕ) : ℝ) / (2 * J) ≤ u := hu.1
    have hdiff : 1 / (2 * J) ≤ (2 * (k : ℕ) : ℝ) / (2 * J) - (2 * (i : ℕ) + 1 : ℝ) / (2 * J) := by
      rw [div_sub_div_same, div_le_div_iff_of_pos_right hJ0]
      linarith
    rw [abs_of_nonpos (by linarith : s - u ≤ 0)]
    linarith
  · have hik1 : ((k : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    have h1 : u ≤ (2 * (k : ℕ) + 1 : ℝ) / (2 * J) := hu.2
    have h2 : (2 * (i : ℕ) : ℝ) / (2 * J) ≤ s := hs.1
    have hdiff : 1 / (2 * J) ≤ (2 * (i : ℕ) : ℝ) / (2 * J) - (2 * (k : ℕ) + 1 : ℝ) / (2 * J) := by
      rw [div_sub_div_same, div_le_div_iff_of_pos_right hJ0]
      linarith
    rw [abs_of_nonneg (by linarith : 0 ≤ s - u)]
    linarith

open GaloisForLFunctions.HTGeometry in
/-- The weights of the window primes. -/
def windowPrimeWeight (x θ : ℝ) : Fin (windowPrimes x (x + x ^ θ)).card → ℝ :=
  fun r => Real.log (windowPrimeIndex x (x + x ^ θ) r)

open GaloisForLFunctions.HTGeometry in
/-- The window primes rescaled to `[0,1]`. -/
def windowPrimeNode (x θ : ℝ) : Fin (windowPrimes x (x + x ^ θ)).card → ℝ :=
  windowNode (windowPrimeIndex x (x + x ^ θ)) x (x + x ^ θ)

/-- The Rayleigh floor of the prime window. -/
def primeWindowFloor (J : ℕ) (θ x : ℝ) : ℝ :=
  (x ^ θ / (32768 * J)) /
    ((J : ℝ) * (2 * ((J : ℝ) * (2 ^ (J - 1) /
      ((1 / (2 * (J : ℝ))) ^ (J - 1) * (((J - 1).factorial : ℕ) : ℝ)))) *
      GaloisForLFunctions.HTGeometry.unitCoeffConstSum J) ^ 2)

theorem eventually_small_ratio {J : ℕ} (hJ : 0 < J) {α θ : ℝ} (hαθ : α < θ) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → 2 * x ^ (α - θ) ≤ 1 / (4 * J) := by
  have hpos : (0:ℝ) < 1 / (4 * J) := by
    have : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
    positivity
  have hneg : 0 < θ - α := by linarith
  have htend : Filter.Tendsto (fun x : ℝ => 2 * x ^ (-(θ - α))) Filter.atTop (nhds 0) := by
    have := tendsto_rpow_neg_atTop hneg
    simpa using this.const_mul (2:ℝ)
  have hev := htend.eventually (eventually_le_nhds hpos)
  obtain ⟨X₀, hX₀⟩ := (Filter.eventually_atTop.1 hev)
  refine ⟨max X₀ 1, le_max_right _ _, fun x hx => ?_⟩
  have h1 : X₀ ≤ x := le_trans (le_max_left _ _) hx
  have := hX₀ x h1
  have hexp : -(θ - α) = α - θ := by ring
  rwa [hexp] at this

open GaloisForLFunctions.HTGeometry in
/-- **The prime window carries a Rayleigh floor.**  For every order `J` there is a threshold beyond
which the moment matrix of the primes of `(x, x + x^θ]`, weighted by `log p` and rescaled to
`[0,1]`, is bounded below by an explicit multiple of the identity. -/
theorem exists_prime_window_rayleigh (J : ℕ) (hJ : 0 < J) {α θ : ℝ}
    (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → ∀ c : Fin J → ℝ,
      primeWindowFloor J θ x * (∑ k, c k ^ 2)
        ≤ c ⬝ᵥ (atomicHankel (windowPrimeWeight x θ) (windowPrimeNode x θ) J).mulVec c := by
  classical
  obtain ⟨X₁, hX₁, hsub⟩ := exists_theta_subwindow_lower halpha hαθ hθ1
  obtain ⟨X₂, hX₂, hratio⟩ := eventually_small_ratio hJ hαθ
  refine ⟨max X₁ X₂, le_trans hX₁ (le_max_left _ _), fun x hx c => ?_⟩
  have hx1 : X₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : X₂ ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (1:ℝ) ≤ x := le_trans hX₁ hx1
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx0
  set Δ : ℝ := x ^ θ with hΔdef
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hxpos θ
  set y : ℝ := x + Δ with hydef
  have hxy : x < y := by
    rw [hydef]
    linarith
  set p : Fin (windowPrimes x y).card → ℕ := windowPrimeIndex x y with hpdef
  set w : Fin (windowPrimes x y).card → ℝ := fun r => Real.log (p r) with hwdef
  set t : Fin (windowPrimes x y).card → ℝ := windowNode p x y with htdef
  have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hη : (0:ℝ) < 1 / (2 * (J : ℝ)) := by positivity
  set m : ℝ := Δ / (32768 * J) with hmdef
  have hm : 0 < m := by
    rw [hmdef]
    positivity
  set A : Fin J → ℝ := fun i => 1 - subwindowRight J i with hAdef
  set Bd : Fin J → ℝ := fun i => 1 - subwindowLeft J i with hBddef
  set Blk : Fin J → Finset (Fin (windowPrimes x y).card) := fun i =>
    {r ∈ Finset.univ | p r ∈ Finset.Ioc ⌊x + subwindowLeft J i * Δ⌋₊
      ⌊x + subwindowRight J i * Δ⌋₊} with hBlkdef
  -- geometry of the subwindows
  have hleft_nonneg : ∀ i : Fin J, 0 ≤ subwindowLeft J i := subwindowLeft_nonneg
  have hlr : ∀ i : Fin J, subwindowLeft J i ≤ subwindowRight J i := fun i =>
    le_of_lt (subwindowLeft_lt_right hJ i)
  have hr1 : ∀ i : Fin J, subwindowRight J i ≤ 1 := subwindowRight_le_one hJ
  have hxu : ∀ i : Fin J, x ≤ x + subwindowLeft J i * Δ := by
    intro i
    nlinarith [hleft_nonneg i, hΔ]
  have huv : ∀ i : Fin J, x + subwindowLeft J i * Δ ≤ x + subwindowRight J i * Δ := by
    intro i
    nlinarith [hlr i, hΔ]
  have hvy : ∀ i : Fin J, x + subwindowRight J i * Δ ≤ y := by
    intro i
    rw [hydef]
    nlinarith [hr1 i, hΔ]
  -- the block masses
  have hmass : ∀ i : Fin J, m ≤ ∑ r ∈ Blk i, w r := by
    intro i
    have hblock : (∑ r ∈ Blk i, w r)
        = Chebyshev.theta (x + subwindowRight J i * Δ)
          - Chebyshev.theta (x + subwindowLeft J i * Δ) := by
      rw [hBlkdef, hwdef, hpdef]
      exact sum_log_windowPrimeIndex_block (huv i) (hxu i) (hvy i)
    rw [hblock]
    have hlow := hsub x hx1 (subwindowLeft J i) (subwindowRight J i) (hleft_nonneg i)
      (hlr i) (hr1 i)
    refine le_trans ?_ hlow
    have hgap : subwindowRight J i - subwindowLeft J i = 1 / (2 * (J : ℝ)) :=
      subwindowRight_sub_left i
    have hsmall : 2 * x ^ (α - θ) ≤ 1 / (4 * (J : ℝ)) := hratio x hx2
    have hkey : 1 / (4 * (J : ℝ))
        ≤ (subwindowRight J i - subwindowLeft J i) - 2 * x ^ (α - θ) := by
      rw [hgap]
      have h2 : 1 / (2 * (J : ℝ)) - 1 / (4 * (J : ℝ)) = 1 / (4 * (J : ℝ)) := by
        field_simp
        ring
      linarith
    rw [hmdef, hΔdef]
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 8192)]
    have hxθ : (0:ℝ) < x ^ θ := Real.rpow_pos_of_pos hxpos θ
    have hJne : (J : ℝ) ≠ 0 := ne_of_gt hJR
    have hprod := mul_le_mul_of_nonneg_right hkey
      (le_of_lt (by positivity : (0:ℝ) < x ^ θ * (32768 * (J : ℝ))))
    calc x ^ θ * 8192 = (1 / (4 * (J : ℝ))) * (x ^ θ * (32768 * (J : ℝ))) := by
          field_simp
          ring
      _ ≤ ((subwindowRight J i - subwindowLeft J i) - 2 * x ^ (α - θ))
            * (x ^ θ * (32768 * (J : ℝ))) := hprod
      _ = ((subwindowRight J i - subwindowLeft J i) - 2 * x ^ (α - θ)) * x ^ θ
            * (32768 * (J : ℝ)) := by ring
  -- blocks are nonempty
  have hBne : ∀ i : Fin J, (Blk i).Nonempty := by
    intro i
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    have := hmass i
    rw [hcon, Finset.sum_empty] at this
    linarith
  -- the nodes of a block lie in the reflected subwindow
  have hBmem : ∀ i : Fin J, ∀ r ∈ Blk i, t r ∈ Set.Icc (A i) (Bd i) := by
    intro i r hr
    have hmem : p r ∈ Finset.Ioc ⌊x + subwindowLeft J i * Δ⌋₊ ⌊x + subwindowRight J i * Δ⌋₊ := by
      have := Finset.mem_filter.1 hr
      exact this.2
    have hmem' := Finset.mem_Ioc.1 hmem
    have hup : (p r : ℝ) ≤ x + subwindowRight J i * Δ := by
      have h1 : (p r : ℝ) ≤ (⌊x + subwindowRight J i * Δ⌋₊ : ℝ) := by exact_mod_cast hmem'.2
      refine le_trans h1 (Nat.floor_le ?_)
      nlinarith [hr1 i, hΔ, hleft_nonneg i, hxpos, hlr i]
    have hlow : x + subwindowLeft J i * Δ < (p r : ℝ) := by
      have h1 : (⌊x + subwindowLeft J i * Δ⌋₊ : ℝ) + 1 ≤ (p r : ℝ) := by
        exact_mod_cast hmem'.1
      have h2 := Nat.lt_floor_add_one (x + subwindowLeft J i * Δ)
      linarith
    have hden : x + Δ - x = Δ := by ring
    constructor
    · show 1 - subwindowRight J i ≤ (x + Δ - (p r : ℝ)) / (x + Δ - x)
      rw [hden, le_div_iff₀ hΔ]
      nlinarith [hup]
    · show (x + Δ - (p r : ℝ)) / (x + Δ - x) ≤ 1 - subwindowLeft J i
      rw [hden, div_le_iff₀ hΔ]
      nlinarith [hlow]
  have hIcc : ∀ i : Fin J, ∀ s ∈ Set.Icc (A i) (Bd i), s ∈ Set.Icc (0:ℝ) 1 := by
    intro i s hs
    constructor
    · have := hr1 i
      have h1 : A i = 1 - subwindowRight J i := rfl
      linarith [hs.1]
    · have := hleft_nonneg i
      have h1 : Bd i = 1 - subwindowLeft J i := rfl
      linarith [hs.2]
  have hsep : ∀ i k : Fin J, i ≠ k → ∀ s ∈ Set.Icc (A i) (Bd i), ∀ u ∈ Set.Icc (A k) (Bd k),
      1 / (2 * (J : ℝ)) ≤ |s - u| := by
    intro i k hik s hs u hu
    have hs' : 1 - s ∈ Set.Icc (subwindowLeft J i) (subwindowRight J i) := by
      constructor
      · have : s ≤ 1 - subwindowLeft J i := hs.2
        linarith
      · have : 1 - subwindowRight J i ≤ s := hs.1
        linarith
    have hu' : 1 - u ∈ Set.Icc (subwindowLeft J k) (subwindowRight J k) := by
      constructor
      · have : u ≤ 1 - subwindowLeft J k := hu.2
        linarith
      · have : 1 - subwindowRight J k ≤ u := hu.1
        linarith
    have := subwindow_separated hJ hik hs' hu'
    have habs : |(1 - s) - (1 - u)| = |s - u| := by
      rw [show (1 - s) - (1 - u) = -(s - u) by ring, abs_neg]
    rwa [habs] at this
  have hwpos : ∀ r, 0 < w r := by
    intro r
    have hp2 : 2 ≤ p r := (windowPrimeIndex_prime x y r).two_le
    have h2 : (2:ℝ) ≤ (p r : ℝ) := by exact_mod_cast hp2
    rw [hwdef]
    exact Real.log_pos (by linarith)
  have hray := rayleigh_lower_of_blocks hJ hη hm A Bd hIcc hsep t w hwpos Blk hBne hBmem hmass c
  rw [dotProduct_mulVec_atomicHankel]
  have hweq : windowPrimeWeight x θ = w := rfl
  have hteq : windowPrimeNode x θ = t := rfl
  rw [hweq, hteq]
  refine le_trans (le_of_eq ?_) hray
  rw [primeWindowFloor, hmdef, hΔdef]

end RHTower.Sieve

end
