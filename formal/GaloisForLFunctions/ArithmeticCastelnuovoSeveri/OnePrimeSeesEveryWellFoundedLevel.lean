import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.AlmostEveryPrimeSeesEveryRightZero

/-!
# One prime sees every well-founded level

A prime tower `g(· − k log p)` sees an outer Frobenius eigenvalue `b = p^{ρ − ½}` of nonzero weight
once the negative vector of `b` lies in the closed span of the tower. Orthogonality to the tower is
a vanishing of all Laurent moments `Σ_τ q_τ β_τ^k`, `k ∈ ℤ`; the finite case separated the classes by
annihilating polynomials (`classSum_eq_zero_of_orthogonal_tower`). Here the classes are extracted
**from the top down**, with no finiteness:

* if every class of modulus `> r` already has zero weight, the moments of the part of modulus `≤ r`
  vanish, and Cesàro means of `(w/c)^n` pick out each class of modulus exactly `r`
  (`tsum_ite_eq_zero_of_moments_of_wellFounded`);
* this induction runs as long as the moduli above `|b|` contain no strictly increasing sequence; for
  the tower the moduli are `p^{Re τ − ½}`, so the condition is on the real parts of the right zeros
  above `Re ρ` and is the same for every prime (`upperLevels`, `classSum_eq_zero_of_wellFounded`).
  The reflected class `1/b̄` is extracted from the bottom up by the negative moments.

Consequences.
* **The tower law without finiteness** (`tower_pontryagin_law_of_wellFounded`). If the real parts of
  the right zeros contain no strictly increasing sequence, at every prime the tower defect equals
  the number of visible outer eigenvalues, finite or infinite, however the eigenvalues accumulate
  in the annulus `1 < |β| < √p`. With a spectrally generic test and a prime separating the right
  zeros, one tower carries the whole, possibly infinite, defect (`tower_defect_eq_encard_of_injOn`).
* **Attained tops are seen by one prime** (`card_le_towerDefect_of_top`). If the largest real part
  of the right zeros is attained, every visible class on the top level is seen by every prime
  tower, with no condition below the top. If the top level is finite, all but finitely many primes
  separate it, and each of their towers of a generic test has at least as many negative squares as
  there are top zeros (`almost_every_prime_sees_the_top`).

The remaining case of Open problem 7 is a strictly increasing sequence of real parts. There the
top-down extraction fails, and the one-sided circle quadratures of
`HTGeometry.CircleQuadratureAnnihilating` (atoms on circles of increasing radius annihilating all
holomorphic moments) show the mechanism by which a class can escape the moments.
-/

open Complex
open scoped ComplexConjugate Classical lp
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### Top-down extraction of classes -/

/-- **Fiberwise vanishing.** If every class `w = v` with `φ(v) ≠ 0` has zero weight, then
`Σ_τ q_τ φ(w_τ) = 0`. -/
theorem tsum_mul_eq_zero_of_classSum {T : Type*} {q w : T → ℂ} {φ : ℂ → ℂ}
    (hs : Summable fun τ => q τ * φ (w τ))
    (hcl : ∀ v, φ v ≠ 0 → ∑' τ, (if w τ = v then q τ else 0) = 0) :
    ∑' τ, q τ * φ (w τ) = 0 := by
  have hfib : HasSum (fun v : ℂ => ∑' τ : w ⁻¹' {v}, q τ * φ (w τ)) (∑' τ, q τ * φ (w τ)) :=
    hs.hasSum.tsum_fiberwise _
  have hz : ∀ v : ℂ, ∑' τ : w ⁻¹' {v}, q τ * φ (w τ) = 0 := by
    intro v
    rw [tsum_subtype (w ⁻¹' {v}) fun τ => q τ * φ (w τ)]
    have hind : ∀ τ, (w ⁻¹' {v}).indicator (fun τ => q τ * φ (w τ)) τ =
        φ v * (if w τ = v then q τ else 0) := fun τ => by
      simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
      split_ifs with h
      · rw [h, mul_comm]
      · rw [mul_zero]
    rw [tsum_congr hind, tsum_mul_left]
    by_cases hφ : φ v = 0
    · rw [hφ, zero_mul]
    · rw [hcl v hφ, mul_zero]
  rw [funext hz] at hfib
  exact hfib.unique hasSum_zero

/-- **Top-down class extraction.** Let `Σ_τ q_τ w_τ^n = 0` for every `n ≥ 0`, with `Σ |q_τ| < ∞` and
`w` bounded. If the moduli `|w_τ| ≥ |c₀|` contain no strictly increasing sequence, the class `w = c₀`
has zero weight. -/
theorem tsum_ite_eq_zero_of_moments_of_wellFounded {T : Type*} {q w : T → ℂ}
    (hq : Summable fun τ => ‖q τ‖) {B : ℝ} (hB : ∀ τ, ‖w τ‖ ≤ B)
    (hm : ∀ n : ℕ, ∑' τ, q τ * w τ ^ n = 0) {c₀ : ℂ} (hc₀ : c₀ ≠ 0)
    (hwf : {x : ℝ | ∃ τ, ‖w τ‖ = x ∧ ‖c₀‖ ≤ x}.WellFoundedOn (· > ·)) :
    ∑' τ, (if w τ = c₀ then q τ else 0) = 0 := by
  have hc₀pos : 0 < ‖c₀‖ := norm_pos_iff.mpr hc₀
  -- the twisted moments are absolutely summable
  have hsum : ∀ (n : ℕ) (φ : ℂ → ℂ), (∀ v, ‖φ v‖ ≤ 1) →
      Summable fun τ => q τ * (φ (w τ) * w τ ^ n) := fun n φ hφ =>
    Summable.of_norm_bounded (hq.mul_right (B ^ n)) fun τ => by
      rw [norm_mul, norm_mul, norm_pow]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc ‖φ (w τ)‖ * ‖w τ‖ ^ n ≤ 1 * B ^ n :=
            mul_le_mul (hφ _) (pow_le_pow_left₀ (norm_nonneg _) (hB τ) n)
              (pow_nonneg (norm_nonneg _) _) zero_le_one
        _ = B ^ n := one_mul _
  suffices key : ∀ x ∈ {x : ℝ | ∃ τ, ‖w τ‖ = x ∧ ‖c₀‖ ≤ x}, ∀ c : ℂ, ‖c‖ = x →
      ∑' τ, (if w τ = c then q τ else 0) = 0 by
    by_cases hex : ∃ τ, w τ = c₀
    · obtain ⟨τ₀, hτ₀⟩ := hex
      exact key ‖c₀‖ ⟨τ₀, by rw [hτ₀], le_rfl⟩ c₀ rfl
    · push Not at hex
      exact (tsum_congr fun τ => if_neg (hex τ)).trans tsum_zero
  intro x hx
  refine hwf.induction hx (P := fun x => ∀ c : ℂ, ‖c‖ = x →
    ∑' τ, (if w τ = c then q τ else 0) = 0) ?_
  intro y hy IH c hc
  obtain ⟨-, -, hy0⟩ := hy
  have hcpos : 0 < ‖c‖ := by rw [hc]; exact lt_of_lt_of_le hc₀pos hy0
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
  -- the part strictly above `y` has vanishing moments, class by class
  have habove : ∀ n : ℕ, ∑' τ, q τ * ((if y < ‖w τ‖ then 1 else 0) * w τ ^ n) = 0 := by
    intro n
    refine tsum_mul_eq_zero_of_classSum (φ := fun v => (if y < ‖v‖ then 1 else 0) * v ^ n)
      (hsum n (fun v => if y < ‖v‖ then 1 else 0) fun v => by split_ifs <;> simp) fun v hv => ?_
    have hyv : y < ‖v‖ := by
      by_contra h
      exact hv (by simp only [if_neg h, zero_mul])
    by_cases hex : ∃ τ, w τ = v
    · obtain ⟨τ₀, hτ₀⟩ := hex
      exact IH ‖v‖ ⟨τ₀, by rw [hτ₀], hy0.trans hyv.le⟩ hyv v rfl
    · push Not at hex
      exact (tsum_congr fun τ => if_neg (hex τ)).trans tsum_zero
  -- Cesàro extraction on the part of modulus at most `y`
  set r : T → ℂ := fun τ => if ‖w τ‖ ≤ y then q τ else 0 with hr
  have hrs : Summable fun τ => ‖r τ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun τ => by
      simp only [hr]; split_ifs <;> simp) hq
  have hz : ∀ τ, r τ ≠ 0 → ‖w τ / c‖ ≤ 1 := by
    intro τ hτ
    have hle : ‖w τ‖ ≤ y := by
      by_contra h
      exact hτ (by simp only [hr, if_neg h])
    rw [norm_div, div_le_one hcpos, hc]
    exact hle
  have hmr : ∀ n : ℕ, ∑' τ, r τ * (w τ / c) ^ n = 0 := by
    intro n
    have e : ∀ τ, r τ * (w τ / c) ^ n = (c ^ n)⁻¹ * (q τ * (1 * w τ ^ n) -
        q τ * ((if y < ‖w τ‖ then 1 else 0) * w τ ^ n)) := fun τ => by
      simp only [hr, div_pow]
      by_cases h : ‖w τ‖ ≤ y
      · rw [if_pos h, if_neg (not_lt.mpr h), div_eq_mul_inv]
        ring
      · rw [if_neg h, if_pos (not_le.mp h)]
        ring
    rw [tsum_congr e, tsum_mul_left,
      (hsum n (fun _ => 1) fun _ => by simp).tsum_sub
        (hsum n (fun v => if y < ‖v‖ then 1 else 0) fun v => by split_ifs <;> simp), habove n]
    simp only [one_mul, hm n, sub_zero, mul_zero]
  have hext := tsum_ite_eq_zero_of_moments hrs hz hmr
  refine (tsum_congr fun τ => ?_).trans hext
  by_cases h : w τ = c
  · have h1 : w τ / c = 1 := by rw [h, div_self hc0]
    have hle : ‖w τ‖ ≤ y := by rw [h, hc]
    rw [if_pos h, if_pos h1]
    simp only [hr, if_pos hle]
  · have h1 : w τ / c ≠ 1 := fun h1 => h ((div_eq_one_iff_eq hc0).mp h1)
    rw [if_neg h, if_neg h1]

/-! ### Levels of right zeros -/

/-- The real parts of the right zeros at or above `Re ρ`. -/
def upperLevels (Z : ZeroConfig) (ρ : ℂ) : Set ℝ :=
  {σ | ∃ τ ∈ rightZeros Z, τ.re = σ ∧ ρ.re ≤ σ}

theorem norm_frobEig_le_iff {ℓ : ℝ} (hℓ : 0 < ℓ) (τ ρ : ℂ) :
    ‖frobEig ℓ ρ‖ ≤ ‖frobEig ℓ τ‖ ↔ ρ.re ≤ τ.re := by
  rw [norm_frobEig, norm_frobEig, Real.exp_le_exp]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

theorem re_eq_of_norm_frobEig_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {τ ρ : ℂ}
    (h : ‖frobEig ℓ τ‖ = ‖frobEig ℓ ρ‖) : τ.re = ρ.re :=
  le_antisymm ((norm_frobEig_le_iff hℓ ρ τ).mp h.le) ((norm_frobEig_le_iff hℓ τ ρ).mp h.ge)

/-- Moduli above a well-founded level form a well-founded set: they are `e^{ℓ(σ − ½)}` for the real
parts `σ` above the level. -/
theorem wellFoundedOn_moduli {Z : ZeroConfig} {ℓ : ℝ} (hℓ : 0 < ℓ) {ρ : ℂ}
    (hwf : (upperLevels Z ρ).WellFoundedOn (· > ·)) {T : Type*} (w : T → ℂ)
    (hw : ∀ τ, ‖frobEig ℓ ρ‖ ≤ ‖w τ‖ → ∃ τ' ∈ rightZeros Z, ‖w τ‖ = ‖frobEig ℓ τ'‖) :
    {x : ℝ | ∃ τ, ‖w τ‖ = x ∧ ‖frobEig ℓ ρ‖ ≤ x}.WellFoundedOn (· > ·) := by
  have hmono : StrictMono fun σ : ℝ => Real.exp (ℓ * (σ - 1 / 2)) := fun a b hab =>
    Real.exp_lt_exp.mpr (by nlinarith)
  have himg : ((fun σ : ℝ => Real.exp (ℓ * (σ - 1 / 2))) '' upperLevels Z ρ).WellFoundedOn
      (· > ·) :=
    Set.wellFoundedOn_image.mpr (hwf.mono' fun a _ b _ h => hmono.lt_iff_lt.mp h)
  refine himg.mono le_rfl ?_
  rintro x ⟨τ, rfl, hx⟩
  obtain ⟨τ', hτ', he⟩ := hw τ hx
  refine ⟨τ'.re, ⟨τ', hτ', rfl, ?_⟩, ?_⟩
  · rw [he] at hx
    exact (norm_frobEig_le_iff hℓ τ' ρ).mp hx
  · show Real.exp (ℓ * (τ'.re - 1 / 2)) = ‖w τ‖
    rw [he, norm_frobEig]

/-! ### Class separation without finiteness -/

theorem norm_conj_frobEig_le (Z : ZeroConfig) {ℓ : ℝ} (hℓ : 0 < ℓ) (τ : Z.carrier) :
    ‖conj (frobEig ℓ τ)‖ ≤ Real.exp (ℓ / 2) := by
  rw [Complex.norm_conj, norm_frobEig, Real.exp_le_exp]
  have := (Z.strip _ τ.2).2
  nlinarith

theorem norm_inv_conj_frobEig_le (Z : ZeroConfig) {ℓ : ℝ} (hℓ : 0 < ℓ) (τ : Z.carrier) :
    ‖(conj (frobEig ℓ τ))⁻¹‖ ≤ Real.exp (ℓ / 2) := by
  rw [norm_inv, Complex.norm_conj, norm_frobEig, ← Real.exp_neg, Real.exp_le_exp]
  have := (Z.strip _ τ.2).1
  nlinarith

/-- The Laurent moments of a vector orthogonal to the tower vanish. -/
theorem tsum_mul_conj_frobEig_zpow_eq_zero (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (ℓ : ℝ) (a : ℓ²(Z.carrier, ℂ))
    (ha : ∀ k : ℤ, inner ℂ (towerVec Z hZ hg hgc ℓ k) a = 0) (k : ℤ) :
    ∑' τ : Z.carrier, conj (zeroCoord Z g τ) * a τ * conj (frobEig ℓ τ) ^ k = 0 := by
  have h := ha k
  rw [lp.inner_eq_tsum] at h
  simpa only [RCLike.inner_apply', towerVec_apply, map_mul, map_zpow₀, mul_comm, mul_left_comm,
    mul_assoc] using h

/-- **Class separation above a well-founded level.** If the real parts of the right zeros above
`Re ρ` contain no strictly increasing sequence, a vector orthogonal to the tower has zero class sums
at `b = p^{ρ − ½}` and at the reflected eigenvalue `1/b̄`. -/
theorem classSum_eq_zero_of_wellFounded (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ) {ρ : ℂ}
    (hρ : ρ ∈ rightZeros Z) (hwf : (upperLevels Z ρ).WellFoundedOn (· > ·))
    (a : ℓ²(Z.carrier, ℂ)) (ha : ∀ k : ℤ, inner ℂ (towerVec Z hZ hg hgc ℓ k) a = 0) :
    (∑' τ : Z.carrier,
        (if frobEig ℓ τ = frobEig ℓ ρ then conj (zeroCoord Z g τ) * a τ else 0)) = 0 ∧
      ∑' τ : Z.carrier, (if frobEig ℓ τ = reflEig (frobEig ℓ ρ) then
        conj (zeroCoord Z g τ) * a τ else 0) = 0 := by
  have hb1 : 1 < ‖frobEig ℓ ρ‖ := (one_lt_norm_frobEig_iff hℓ ρ).mpr hρ.2
  have hb0 : frobEig ℓ ρ ≠ 0 := frobEig_ne_zero ℓ ρ
  have hq := summable_conj_zeroCoord_mul Z hZ hg hgc a
  have hmom := tsum_mul_conj_frobEig_zpow_eq_zero Z hZ hg hgc ℓ a ha
  constructor
  · -- the outer class, from the top down
    have hw := wellFoundedOn_moduli hℓ hwf (fun τ : Z.carrier => conj (frobEig ℓ τ))
      fun τ hτ => by
        have hτ' : ‖frobEig ℓ ρ‖ ≤ ‖frobEig ℓ τ‖ := by simpa using hτ
        exact ⟨τ, ⟨τ.2, (one_lt_norm_frobEig_iff hℓ _).mp (hb1.trans_le hτ')⟩,
          Complex.norm_conj _⟩
    have h := tsum_ite_eq_zero_of_moments_of_wellFounded hq (w := fun τ => conj (frobEig ℓ τ))
      (norm_conj_frobEig_le Z hℓ)
      (fun n => (tsum_congr fun τ => by rw [zpow_natCast]).trans (hmom n))
      ((map_ne_zero _).mpr hb0) (by simpa only [Complex.norm_conj] using hw)
    simpa only [(starRingEnd ℂ).injective.eq_iff] using h
  · -- the reflected class, from the bottom up
    have e : ∀ β : ℂ, (conj β)⁻¹ = frobEig ℓ ρ ↔ β = reflEig (frobEig ℓ ρ) := fun β => by
      constructor
      · intro h; rw [reflEig, ← h, map_inv₀, Complex.conj_conj, inv_inv]
      · intro h; rw [h, reflEig, map_inv₀, Complex.conj_conj, inv_inv]
    have hw := wellFoundedOn_moduli hℓ hwf (fun τ : Z.carrier => (conj (frobEig ℓ τ))⁻¹)
      fun τ hτ => by
        have hτ' : ‖frobEig ℓ ρ‖ ≤ ‖frobEig ℓ τ‖⁻¹ := by simpa using hτ
        have hlt : ‖frobEig ℓ τ‖ < 1 := by
          have := hb1.trans_le hτ'
          rwa [one_lt_inv₀ (norm_pos_iff.mpr (frobEig_ne_zero ℓ τ))] at this
        have hre : (τ : ℂ).re < 1 / 2 := (norm_frobEig_lt_one_iff hℓ _).mp hlt
        refine ⟨reflect (τ : ℂ), ⟨Z.reflect_mem _ τ.2, ?_⟩, ?_⟩
        · rw [re_reflect]; linarith
        · simp only [norm_inv, Complex.norm_conj, frobEig_reflect]
    have h := tsum_ite_eq_zero_of_moments_of_wellFounded hq
      (w := fun τ => (conj (frobEig ℓ τ))⁻¹) (norm_inv_conj_frobEig_le Z hℓ)
      (fun n => (tsum_congr fun τ => by rw [zpow_neg, zpow_natCast, inv_pow]).trans
        (hmom (-(n : ℤ))))
      hb0 hw
    simpa only [e] using h

/-- **The negative vector of a well-founded eigenvalue lies in the closed span of the tower.** -/
theorem eigTarget_mem_closure_of_wellFounded (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ) {ρ : ℂ}
    (hρ : ρ ∈ rightZeros Z) (hwf : (upperLevels Z ρ).WellFoundedOn (· > ·)) :
    eigTarget Z hZ hg hgc ℓ (frobEig ℓ ρ) ∈
      (Submodule.span ℂ (Set.range (towerVec Z hZ hg hgc ℓ))).topologicalClosure :=
  eigTarget_mem_closure_of_classSum Z hZ hg hgc _ fun a ha =>
    classSum_eq_zero_of_wellFounded Z hZ hg hgc hℓ hρ hwf a ha

/-! ### The tower law without finiteness -/

/-- The visible outer eigenvalues: those of nonzero Frobenius weight. -/
def visibleSet (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) : Set ℂ :=
  {b | b ∈ outerEig Z ℓ ∧ frobWeight Z g ℓ b ≠ 0}

/-- **Attainment above well-founded levels.** Finitely many visible eigenvalues, each above a
well-founded level, are seen together by one window of the tower. -/
theorem card_le_towerDefect_of_wellFounded (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ) (O : Finset ℂ)
    (hO : ∀ b ∈ O, b ∈ visibleSet Z g ℓ)
    (hwf : ∀ b ∈ O, ∃ ρ ∈ rightZeros Z, frobEig ℓ ρ = b ∧
      (upperLevels Z ρ).WellFoundedOn (· > ·)) :
    ∃ K : Finset ℤ, O.card ≤ hermNegIndex (towerGram Z g ℓ K) :=
  exists_towerGram_negIndex_ge_of_closure Z hZ hg hgc hℓ O hO fun b hb => by
    obtain ⟨ρ, hρ, rfl, hw⟩ := hwf b hb
    exact eigTarget_mem_closure_of_wellFounded Z hZ hg hgc hℓ hρ hw

/-- **The tower Pontryagin law without finiteness.** If the real parts of the right zeros contain no
strictly increasing sequence, the Weil form has `n` negative squares on some window of the tower
`g(· − k ℓ)` iff at least `n` outer eigenvalues have nonzero Frobenius weight. -/
theorem tower_pontryagin_law_of_wellFounded (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hWF : (Complex.re '' rightZeros Z).WellFoundedOn (· > ·)) (n : ℕ) :
    (∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K)) ↔
      (n : ℕ∞) ≤ (visibleSet Z g ℓ).encard := by
  constructor
  · rintro ⟨K, hK⟩
    by_cases hfin : (visibleSet Z g ℓ).Finite
    · rw [hfin.encard_eq_coe_toFinset_card]
      exact_mod_cast hK.trans (negIndex_towerGram_le_of_visible_subset Z hZ hg hgc hℓ
        hfin.toFinset (fun b hb hne => hfin.mem_toFinset.mpr ⟨hb, hne⟩) K)
    · rw [Set.Infinite.encard_eq hfin]
      exact le_top
  · intro hn
    obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq hn
    have htfin : t.Finite := Set.finite_of_encard_eq_coe htc
    obtain ⟨K, hK⟩ := card_le_towerDefect_of_wellFounded Z hZ hg hgc hℓ htfin.toFinset
      (fun b hb => hts (htfin.mem_toFinset.mp hb)) fun b hb => by
        obtain ⟨ρ, hρ, rfl⟩ := (hts (htfin.mem_toFinset.mp hb)).1
        refine ⟨ρ, hρ, rfl, hWF.mono le_rfl ?_⟩
        rintro σ ⟨τ, hτ, rfl, -⟩
        exact ⟨τ, hτ, rfl⟩
    refine ⟨K, le_trans ?_ hK⟩
    have hcard : (htfin.toFinset.card : ℕ∞) = n := by
      rw [← htfin.encard_eq_coe_toFinset_card, htc]
    exact_mod_cast hcard.ge

/-- At a scale separating the right zeros, the Frobenius weight of each outer eigenvalue is a single
nonzero term, so every outer eigenvalue is visible for a spectrally generic test. -/
theorem visibleSet_eq_of_injOn (Z : ZeroConfig) {g : ℝ → ℂ} (hgen : SpectrallyGeneric Z g)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hinj : Set.InjOn (frobEig ℓ) (rightZeros Z)) :
    visibleSet Z g ℓ = outerEig Z ℓ := by
  ext b
  refine ⟨fun hb => hb.1, fun hb => ⟨hb, ?_⟩⟩
  obtain ⟨ρ, hρ, rfl⟩ := hb
  exact frobWeight_ne_zero_of_injOn Z hgen hℓ hinj hρ

/-- **One prime carries the whole, possibly infinite, defect.** If the real parts of the right zeros
contain no strictly increasing sequence and `frobEig ℓ` separates the right zeros, the tower of a
spectrally generic test has `n` negative squares on some window iff there are at least `n` right
zeros. -/
theorem tower_defect_eq_encard_of_injOn (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hgen : SpectrallyGeneric Z g) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hWF : (Complex.re '' rightZeros Z).WellFoundedOn (· > ·))
    (hinj : Set.InjOn (frobEig ℓ) (rightZeros Z)) (n : ℕ) :
    (∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K)) ↔
      (n : ℕ∞) ≤ (rightZeros Z).encard := by
  rw [tower_pontryagin_law_of_wellFounded Z hZ hg hgc hℓ hWF n,
    visibleSet_eq_of_injOn Z hgen hℓ hinj, outerEig, hinj.encard_image]

/-! ### Attained tops -/

/-- At an attained top every level above a top zero is the top itself. -/
theorem upperLevels_wellFounded_of_top {Z : ZeroConfig} {ρ₀ ρ : ℂ}
    (htop : ∀ τ ∈ rightZeros Z, τ.re ≤ ρ₀.re) (hρ : ρ.re = ρ₀.re) :
    (upperLevels Z ρ).WellFoundedOn (· > ·) := by
  refine ((Set.finite_singleton ρ₀.re).subset ?_).wellFoundedOn
  rintro σ ⟨τ, hτ, rfl, hle⟩
  exact le_antisymm (htop τ hτ) (by rw [← hρ]; exact hle)

/-- **Attained tops are seen by every prime.** If the largest real part `Re ρ₀` of the right zeros
is attained, any finitely many visible eigenvalues on the top circle `|b| = p^{Re ρ₀ − ½}` are seen
together by one window of the tower. -/
theorem card_le_towerDefect_of_top (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ) {ρ₀ : ℂ}
    (htop : ∀ τ ∈ rightZeros Z, τ.re ≤ ρ₀.re) (O : Finset ℂ)
    (hO : ∀ b ∈ O, b ∈ visibleSet Z g ℓ ∧ ‖b‖ = ‖frobEig ℓ ρ₀‖) :
    ∃ K : Finset ℤ, O.card ≤ hermNegIndex (towerGram Z g ℓ K) :=
  card_le_towerDefect_of_wellFounded Z hZ hg hgc hℓ O (fun b hb => (hO b hb).1) fun b hb => by
    obtain ⟨⟨ρ, hρ, rfl⟩, -⟩ := (hO b hb).1
    exact ⟨ρ, hρ, rfl, upperLevels_wellFounded_of_top htop
      (re_eq_of_norm_frobEig_eq hℓ (hO _ hb).2)⟩

/-- The right zeros on the level of `ρ₀`. -/
def topZeros (Z : ZeroConfig) (ρ₀ : ℂ) : Set ℂ := {τ | τ ∈ rightZeros Z ∧ τ.re = ρ₀.re}

/-- At a scale separating the top zeros, the weight of the eigenvalue of a top zero is a single
nonzero term: no zero off the top shares its modulus. -/
theorem frobWeight_ne_zero_of_top (Z : ZeroConfig) {g : ℝ → ℂ} (hgen : SpectrallyGeneric Z g)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {ρ₀ : ℂ} (hinj : Set.InjOn (frobEig ℓ) (topZeros Z ρ₀)) {ρ : ℂ}
    (hρ : ρ ∈ topZeros Z ρ₀) : frobWeight Z g ℓ (frobEig ℓ ρ) ≠ 0 := by
  rw [frobWeight, tsum_eq_single (⟨ρ, hρ.1.1⟩ : Z.carrier) (fun τ hτ => ?_)]
  · rw [if_pos rfl]
    exact mul_ne_zero (zeroCoord_ne_zero hgen _) ((map_ne_zero _).mpr (zeroCoord_ne_zero hgen _))
  · rw [if_neg]
    intro he
    have hre : (τ : ℂ).re = ρ₀.re :=
      (re_eq_of_norm_frobEig_eq hℓ (congrArg norm he)).trans hρ.2
    have hright : (τ : ℂ) ∈ rightZeros Z := ⟨τ.2, by rw [hre]; exact hρ.1.2.trans_eq hρ.2⟩
    exact hτ (Subtype.ext (hinj ⟨hright, hre⟩ hρ he))

/-- At most finitely many primes fail to separate a finite set of points by their Frobenius
eigenvalues. -/
theorem finite_resonantPrimes_of_finite {S : Set ℂ} (hS : S.Finite) :
    {p : ℕ | p.Prime ∧ ¬ Set.InjOn (frobEig (Real.log p)) S}.Finite := by
  have hsub : {p : ℕ | p.Prime ∧ ¬ Set.InjOn (frobEig (Real.log p)) S} ⊆
      ⋃ ρ ∈ S, ⋃ ρ' ∈ S,
        {p : ℕ | ρ ≠ ρ' ∧ p.Prime ∧ frobEig (Real.log p) ρ = frobEig (Real.log p) ρ'} := by
    rintro p ⟨hp, hinj⟩
    simp only [Set.InjOn, not_forall, exists_prop] at hinj
    obtain ⟨ρ, hρ, ρ', hρ', he, hne⟩ := hinj
    simp only [Set.mem_iUnion]
    exact ⟨ρ, hρ, ρ', hρ', hne, hp, he⟩
  refine Set.Finite.subset (hS.biUnion fun ρ _ => hS.biUnion fun ρ' _ => ?_) hsub
  by_cases hne : ρ = ρ'
  · simp [hne]
  · refine (subsingleton_resonantPrimes hne).finite.subset ?_
    rintro p ⟨-, hp, he⟩
    exact ⟨hp, he⟩

/-- **Almost every prime sees an attained finite top.** If the largest real part of the right zeros
is attained by finitely many zeros, all but finitely many primes separate them, and at each such
prime the tower of a spectrally generic test has at least as many negative squares on some window
as there are top zeros. -/
theorem almost_every_prime_sees_the_top (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hgen : SpectrallyGeneric Z g) {ρ₀ : ℂ}
    (htop : ∀ τ ∈ rightZeros Z, τ.re ≤ ρ₀.re) (hfin : (topZeros Z ρ₀).Finite) :
    {p : ℕ | p.Prime ∧ ¬ Set.InjOn (frobEig (Real.log p)) (topZeros Z ρ₀)}.Finite ∧
      ∀ p : ℕ, p.Prime → Set.InjOn (frobEig (Real.log p)) (topZeros Z ρ₀) →
        ∃ K : Finset ℤ, hfin.toFinset.card ≤ hermNegIndex (towerGram Z g (Real.log p) K) := by
  refine ⟨finite_resonantPrimes_of_finite hfin, fun p hp hinj => ?_⟩
  have hℓ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  obtain ⟨K, hK⟩ := card_le_towerDefect_of_top Z hZ hg hgc hℓ htop
    (hfin.toFinset.image (frobEig (Real.log p))) fun b hb => by
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hb
      have hρ' := hfin.mem_toFinset.mp hρ
      refine ⟨⟨⟨ρ, hρ'.1, rfl⟩, frobWeight_ne_zero_of_top Z hgen hℓ hinj hρ'⟩, ?_⟩
      rw [norm_frobEig, norm_frobEig, hρ'.2]
  refine ⟨K, le_trans (Finset.card_image_of_injOn fun x hx y hy hxy =>
    hinj (hfin.mem_toFinset.mp hx) (hfin.mem_toFinset.mp hy) hxy).ge hK⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
