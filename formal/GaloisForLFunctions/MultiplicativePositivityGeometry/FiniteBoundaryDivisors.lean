import GaloisForLFunctions.MultiplicativePositivityGeometry.TotalZeroMass
import GaloisForLFunctions.MultiplicativePositivityGeometry.IntegralRealization

/-!
# Finite boundary divisors: Bochner's theorem on the discrete line

A finite boundary configuration is an even function `D` on `ℝ` supported on `{0} ∪ ±Z`, where `Z` is
a finite set of positive heights (`IsFiniteConfig`). Poles and zeros may sit at arbitrary real
heights, with no commensurability; poles off the origin are allowed. Its Bohr polynomial is
`P_D(t) = D(0) + 2 Σ_{z ∈ Z} D(z) cos(zt)` (`bohrPoly`). The following are equivalent:

1. `D` is the boundary divisor of a family of nonnegative weights;
2. `D` is positive definite on `ℝ`;
3. `P_D(t) ≥ 0` for every real `t`;
4. `D` is the boundary divisor of an Euler product `Π_p (1 − p^{−s})^{−m(p)}` with integer
   exponents `m(p) ≥ 0`.

(1 ⇒ 2) is boundary positivity. (2 ⇒ 3) (`bohrPoly_nonneg`): the Gram forms with coefficients
`cos(tx)` and `sin(tx)` over the Følner sets `F_N = {Σ n_z z}` add up to
`Σ_{x,y ∈ F_N} D(x − y) cos(t(x − y)) = |F_N| D(0) + 2 Σ_z D(z) cos(tz) · #{y : y, y + z ∈ F_N}`,
and the counts are `≥ (1 − ε)|F_N|` at a slow step of the Følner sequence. (3 ⇒ 1)
(`bohr_isBoundaryDivisor`): the von Mangoldt weights twisted by `P_D(log n)` are the
log-derivative coefficients of `ζ(s)^{D(0)} Π_{z ∈ Z} (ζ(s + iz) ζ(s − iz))^{D(z)}`, whose boundary
divisor is `D`. (3 ⇒ 4) is greedy rounding (`IsBoundaryDivisor.round`).

The progression characterization (`boundary_profile_iff`) is the case `Z ⊂ t₀ℕ`. Here no lattice is
assumed: the boundary positivity theorem has an exact converse for every finite configuration.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-! ### Almost-periodic twists of the von Mangoldt weights -/

/-- The almost-periodic polynomial `c₀ + Σ_{z ∈ Z} b(z) cos(zt)`. -/
noncomputable def apPoly (c₀ : ℝ) (Z : Finset ℝ) (b : ℝ → ℝ) (t : ℝ) : ℝ :=
  c₀ + ∑ z ∈ Z, b z * Real.cos (z * t)

/-- Its divisor `c₀ δ₀ + Σ_z (b(z)/2)(δ_{−z} + δ_z)`. -/
noncomputable def apDivisor (c₀ : ℝ) (Z : Finset ℝ) (b : ℝ → ℝ) (u : ℝ) : ℝ :=
  c₀ * diracAt u + ∑ z ∈ Z, b z / 2 * (diracAt (u + z) + diracAt (u - z))

/-- Von Mangoldt weights twisted by `apPoly(log n)`. -/
noncomputable def apWeight (c₀ : ℝ) (Z : Finset ℝ) (b : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  zetaBoundaryWeight x n * apPoly c₀ Z b (logFrequency n)

theorem abs_apPoly_le (c₀ : ℝ) (Z : Finset ℝ) (b : ℝ → ℝ) (t : ℝ) :
    |apPoly c₀ Z b t| ≤ |c₀| + ∑ z ∈ Z, |b z| := by
  unfold apPoly
  refine (abs_add_le _ _).trans (add_le_add_right ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun z _ => ?_)) _)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- Product-to-sum for one almost-periodic mode. -/
theorem ap_mode (w L u z bz : ℝ) :
    w * (bz * Real.cos (z * L)) * Real.cos (L * u) =
      bz / 2 * (w * Real.cos (L * (u + z)) + w * Real.cos (L * (u - z))) := by
  have h1 : L * (u + z) = L * u + z * L := by ring
  have h2 : L * (u - z) = L * u - z * L := by ring
  rw [h1, h2, Real.cos_add, Real.cos_sub]
  ring

theorem cosineTrace_apWeight {c₀ : ℝ} {Z : Finset ℝ} {b : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (u : ℝ) :
    cosineTrace (apWeight c₀ Z b x) logFrequency u =
      c₀ * cosineTrace (zetaBoundaryWeight x) logFrequency u +
      ∑ z ∈ Z, b z / 2 * (cosineTrace (zetaBoundaryWeight x) logFrequency (u + z) +
        cosineTrace (zetaBoundaryWeight x) logFrequency (u - z)) := by
  have hz := summable_zetaBoundaryWeight hx
  have hnn := zetaBoundaryWeight_nonneg x
  have hS : HasSum (fun n => c₀ * (zetaBoundaryWeight x n * Real.cos (logFrequency n * u)) +
      ∑ z ∈ Z, b z / 2 *
        (zetaBoundaryWeight x n * Real.cos (logFrequency n * (u + z)) +
          zetaBoundaryWeight x n * Real.cos (logFrequency n * (u - z))))
      (c₀ * cosineTrace (zetaBoundaryWeight x) logFrequency u +
      ∑ z ∈ Z, b z / 2 * (cosineTrace (zetaBoundaryWeight x) logFrequency (u + z) +
        cosineTrace (zetaBoundaryWeight x) logFrequency (u - z))) :=
    ((summable_cosineTrace_terms hnn hz logFrequency u).hasSum.mul_left c₀).add
      (hasSum_sum fun z _ => (((summable_cosineTrace_terms hnn hz logFrequency _).hasSum).add
        ((summable_cosineTrace_terms hnn hz logFrequency _).hasSum)).mul_left _)
  rw [← hS.tsum_eq]
  unfold cosineTrace
  refine tsum_congr fun n => ?_
  unfold apWeight apPoly
  rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun z _ => ap_mode _ _ _ _ _

/-- **Almost-periodic realization.** If `c₀ + Σ_z b(z) cos(zt) ≥ 0`, the twisted von Mangoldt weights
have boundary divisor `c₀ δ₀ + Σ_z (b(z)/2)(δ_{−z} + δ_z)`. -/
theorem ap_isBoundaryDivisor {c₀ : ℝ} {Z : Finset ℝ} {b : ℝ → ℝ}
    (hP : ∀ t, 0 ≤ apPoly c₀ Z b t) :
    IsBoundaryDivisor logFrequency (apWeight c₀ Z b) (apDivisor c₀ Z b) where
  nonneg x _ n := mul_nonneg (zetaBoundaryWeight_nonneg x n) (hP _)
  summable x hx := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (zetaBoundaryWeight_nonneg x n) (hP _))
    (fun n => mul_le_mul_of_nonneg_left ((le_abs_self _).trans (abs_apPoly_le c₀ Z b _))
      (zetaBoundaryWeight_nonneg x n))
    ((summable_zetaBoundaryWeight hx).mul_right _)
  tendsto u := by
    have h : Tendsto (fun x => c₀ * (x * cosineTrace (zetaBoundaryWeight x) logFrequency u) +
        ∑ z ∈ Z, b z / 2 * (x * cosineTrace (zetaBoundaryWeight x) logFrequency (u + z) +
          x * cosineTrace (zetaBoundaryWeight x) logFrequency (u - z))) (𝓝[>] 0)
        (𝓝 (c₀ * zetaBoundaryDivisor u + ∑ z ∈ Z, b z / 2 *
          (zetaBoundaryDivisor (u + z) + zetaBoundaryDivisor (u - z)))) :=
      ((zeta_isBoundaryDivisor.tendsto u).const_mul c₀).add (tendsto_finsetSum _ fun z _ =>
        ((zeta_isBoundaryDivisor.tendsto _).add (zeta_isBoundaryDivisor.tendsto _)).const_mul _)
    have heq : c₀ * zetaBoundaryDivisor u + ∑ z ∈ Z, b z / 2 *
        (zetaBoundaryDivisor (u + z) + zetaBoundaryDivisor (u - z)) = apDivisor c₀ Z b u := by
      simp only [zetaBoundaryDivisor_eq, apDivisor, diracAt]
    rw [heq] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [cosineTrace_apWeight (Set.mem_Ioi.mp hx), mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun z _ => by ring

/-! ### Finite configurations and their Bohr polynomials -/

/-- `D` is even and supported on `{0} ∪ ±Z`, with `Z` a finite set of positive heights. -/
structure IsFiniteConfig (D : ℝ → ℝ) (Z : Finset ℝ) : Prop where
  pos : ∀ z ∈ Z, 0 < z
  even : ∀ u, D (-u) = D u
  supp : ∀ u, u ≠ 0 → |u| ∉ Z → D u = 0

/-- The Bohr polynomial `P_D(t) = D(0) + 2 Σ_{z ∈ Z} D(z) cos(zt)`. -/
noncomputable def bohrPoly (D : ℝ → ℝ) (Z : Finset ℝ) (t : ℝ) : ℝ :=
  apPoly (D 0) Z (fun z => 2 * D z) t

/-- The almost-periodic divisor of the Bohr polynomial is `D` itself. -/
theorem apDivisor_bohr {D : ℝ → ℝ} {Z : Finset ℝ} (hD : IsFiniteConfig D Z) :
    apDivisor (D 0) Z (fun z => 2 * D z) = D := by
  funext u
  unfold apDivisor diracAt
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · have h : ∀ z ∈ Z, 2 * D z / 2 * ((if u + z = 0 then (1 : ℝ) else 0) +
        (if u - z = 0 then 1 else 0)) = if z = -u then D (-u) else 0 := by
      intro z hz
      have hz0 := hD.pos z hz
      have h1 : u - z ≠ 0 := (by linarith : u - z < 0).ne
      by_cases hzu : z = -u
      · rw [if_pos hzu, if_pos (by rw [hzu]; ring), if_neg h1, hzu]
        ring
      · rw [if_neg hzu, if_neg (fun h => hzu (by linarith)), if_neg h1]
        ring
    rw [if_neg hu.ne, Finset.sum_congr rfl h, Finset.sum_ite_eq' Z (-u) (fun _ => D (-u))]
    split_ifs with hmem
    · rw [hD.even]
      ring
    · rw [hD.supp u hu.ne (by rwa [abs_of_neg hu])]
      ring
  · rw [if_pos rfl, Finset.sum_eq_zero fun z hz => ?_]
    · ring
    · have hz0 := hD.pos z hz
      rw [if_neg (by linarith), if_neg (by linarith)]
      ring
  · have h : ∀ z ∈ Z, 2 * D z / 2 * ((if u + z = 0 then (1 : ℝ) else 0) +
        (if u - z = 0 then 1 else 0)) = if z = u then D u else 0 := by
      intro z hz
      have hz0 := hD.pos z hz
      have h1 : u + z ≠ 0 := (by linarith : 0 < u + z).ne'
      by_cases hzu : z = u
      · rw [if_pos hzu, if_neg h1, if_pos (by rw [hzu]; ring), hzu]
        ring
      · rw [if_neg hzu, if_neg h1, if_neg (fun h => hzu (by linarith))]
        ring
    rw [if_neg hu.ne', Finset.sum_congr rfl h, Finset.sum_ite_eq' Z u (fun _ => D u)]
    split_ifs with hmem
    · ring
    · rw [hD.supp u hu.ne' (by rwa [abs_of_pos hu])]
      ring

/-- **Realization (3 ⇒ 1).** A finite configuration with nonnegative Bohr polynomial is the boundary
divisor of `ζ(s)^{D(0)} Π_z (ζ(s + iz) ζ(s − iz))^{D(z)}`. -/
theorem bohr_isBoundaryDivisor {D : ℝ → ℝ} {Z : Finset ℝ} (hD : IsFiniteConfig D Z)
    (hP : ∀ t, 0 ≤ bohrPoly D Z t) :
    IsBoundaryDivisor logFrequency (apWeight (D 0) Z (fun z => 2 * D z)) D := by
  have h := ap_isBoundaryDivisor hP
  rwa [apDivisor_bohr hD] at h

/-! ### Positive definiteness forces a nonnegative Bohr polynomial -/

/-- Gram forms over a finite set with arbitrary coefficients. -/
theorem IsEvenPosDef.sum_finset_mul_nonneg {G : Type*} [AddCommGroup G] {φ : G → ℝ}
    (hφ : IsEvenPosDef φ) (F : Finset G) (c : G → ℝ) :
    0 ≤ ∑ x ∈ F, ∑ y ∈ F, c x * c y * φ (x - y) := by
  have key : ∀ f : G → G → ℝ, ∑ i : Fin F.card, ∑ j : Fin F.card,
      f (F.equivFin.symm i) (F.equivFin.symm j) = ∑ x ∈ F, ∑ y ∈ F, f x y := by
    intro f
    rw [← Finset.sum_coe_sort F, ← Equiv.sum_comp F.equivFin.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort F, ← Equiv.sum_comp F.equivFin.symm]
  have h := hφ.posDef F.card (fun i => (F.equivFin.symm i : G)) (fun i => c (F.equivFin.symm i))
  exact h.trans_eq (key fun x y => c x * c y * φ (x - y))

/-- **Bochner direction (2 ⇒ 3).** A positive-definite finite configuration has a nonnegative Bohr
polynomial at every real `t`. -/
theorem bohrPoly_nonneg {D : ℝ → ℝ} {Z : Finset ℝ} (hD : IsFiniteConfig D Z)
    (hpd : IsEvenPosDef D) (t : ℝ) : 0 ≤ bohrPoly D Z t := by
  classical
  set f : ℝ → ℝ := fun v => D v * Real.cos (t * v) with hf
  -- Sum of the `cos` and `sin` Gram forms.
  have hgram : ∀ F : Finset ℝ, 0 ≤ ∑ x ∈ F, ∑ y ∈ F, f (x - y) := by
    intro F
    have h1 := hpd.sum_finset_mul_nonneg F (fun x => Real.cos (t * x))
    have h2 := hpd.sum_finset_mul_nonneg F (fun x => Real.sin (t * x))
    have hsplit : ∑ x ∈ F, ∑ y ∈ F, f (x - y) =
        ∑ x ∈ F, ∑ y ∈ F, Real.cos (t * x) * Real.cos (t * y) * D (x - y) +
          ∑ x ∈ F, ∑ y ∈ F, Real.sin (t * x) * Real.sin (t * y) * D (x - y) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hf]
      simp only
      rw [show t * (x - y) = t * x - t * y by ring, Real.cos_sub]
      ring
    linarith
  -- Each pair contributes `f 0`, `f(±z)` or nothing.
  have hpt : ∀ x y : ℝ, f (x - y) = (if x = y then f 0 else 0) +
      (if x - y ∈ Z then f (x - y) else 0) + (if y - x ∈ Z then f (y - x) else 0) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      have h0 : (0 : ℝ) ∉ Z := fun h => lt_irrefl 0 (hD.pos 0 h)
      simp [h0]
    · rw [if_neg hxy]
      by_cases h1 : x - y ∈ Z
      · have h2 : y - x ∉ Z := fun h => by
          have := hD.pos _ h
          have := hD.pos _ h1
          linarith
        rw [if_pos h1, if_neg h2]
        ring
      · rw [if_neg h1]
        by_cases h2 : y - x ∈ Z
        · rw [if_pos h2, hf]
          simp only
          rw [show y - x = -(x - y) by ring, hD.even, mul_neg, Real.cos_neg]
          ring
        · rw [if_neg h2, hf]
          simp only
          have hz : D (x - y) = 0 := hD.supp _ (sub_ne_zero.mpr hxy) (by
            rcases abs_choice (x - y) with h | h
            · rw [h]; exact h1
            · rw [h, neg_sub]; exact h2)
          rw [hz]
          ring
  have hf0 : f 0 = D 0 := by simp [hf]
  have hfz : ∀ z, f z = D z * Real.cos (z * t) := fun z => by simp only [hf, mul_comm t z]
  -- The Gram form over a Følner set, grouped by differences.
  have hfol : ∀ N, 0 ≤ ((folnerSet Z N).card : ℝ) * D 0 +
      2 * ∑ z ∈ Z, f z * ((folnerSet Z N).filter fun y => y + z ∈ folnerSet Z N).card := by
    intro N
    have h0 := hgram (folnerSet Z N)
    have hsum : ∑ x ∈ folnerSet Z N, ∑ y ∈ folnerSet Z N, f (x - y) =
        ∑ x ∈ folnerSet Z N, ∑ y ∈ folnerSet Z N, ((if x = y then f 0 else 0) +
          (if x - y ∈ Z then f (x - y) else 0) + (if y - x ∈ Z then f (y - x) else 0)) :=
      Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hpt x y
    have hdiag : ∑ x ∈ folnerSet Z N, ∑ y ∈ folnerSet Z N, (if x = y then f 0 else 0) =
        ((folnerSet Z N).card : ℝ) * f 0 := by
      rw [Finset.sum_congr rfl fun x hx => by rw [Finset.sum_ite_eq, if_pos hx],
        Finset.sum_const, nsmul_eq_mul]
    have h1 := sum_sum_ite_mem (folnerSet Z N) Z f
    have h2 : ∑ x ∈ folnerSet Z N, ∑ y ∈ folnerSet Z N, (if y - x ∈ Z then f (y - x) else 0) =
        ∑ z ∈ Z, f z * ((folnerSet Z N).filter fun y => y + z ∈ folnerSet Z N).card := by
      rw [Finset.sum_comm]
      exact sum_sum_ite_mem (folnerSet Z N) Z f
    simp only [Finset.sum_add_distrib] at hsum
    rw [hsum, hdiag, h1, h2, hf0] at h0
    linarith
  -- At a slow step every shift count is at least `(1 − ε)|F_N|`.
  by_contra hneg
  push Not at hneg
  set B := ∑ z ∈ Z, |D z|
  set ε := -bohrPoly D Z t / (4 * (B + 1)) with hε
  have hB : 0 ≤ B := Finset.sum_nonneg fun z _ => abs_nonneg _
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  obtain ⟨N, hN1, hN⟩ := exists_folner_step Z hε0
  have hF : (0 : ℝ) < (folnerSet Z N).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, zero_mem_folnerSet Z hN1⟩
  set F := ((folnerSet Z N).card : ℝ)
  have hcnt : ∀ z ∈ Z, f z * ((folnerSet Z N).filter fun y => y + z ∈ folnerSet Z N).card ≤
      f z * F + |D z| * (ε * F) := by
    intro z hz
    set c := (((folnerSet Z N).filter fun y => y + z ∈ folnerSet Z N).card : ℝ)
    have hlo : (1 - ε) * F ≤ c := by linarith [card_shift_mem_ge (N := N) hz]
    have hhi : c ≤ F := Nat.cast_le.mpr (Finset.card_filter_le _ _)
    have hfz' : |f z| ≤ |D z| := by
      rw [hfz, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    have hdiff : f z * (c - F) ≤ |D z| * (ε * F) :=
      calc f z * (c - F) ≤ |f z * (c - F)| := le_abs_self _
        _ = |f z| * (F - c) := by rw [abs_mul, abs_of_nonpos (show c - F ≤ 0 by linarith), neg_sub]
        _ ≤ |D z| * (ε * F) :=
          mul_le_mul hfz' (by linarith) (by linarith) (abs_nonneg _)
    linarith
  have hsum := Finset.sum_le_sum hcnt
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul] at hsum
  have hP : bohrPoly D Z t = D 0 + 2 * ∑ z ∈ Z, f z := by
    unfold bohrPoly apPoly
    rw [Finset.mul_sum]
    exact congrArg _ (Finset.sum_congr rfl fun z _ => by rw [hfz]; ring)
  have key : 0 ≤ F * (bohrPoly D Z t + 2 * ε * B) := by
    have := hfol N
    rw [hP]
    nlinarith
  have := (mul_nonneg_iff_of_pos_left hF).mp key
  have hεB : 2 * ε * B < -bohrPoly D Z t := by
    rw [hε]
    rw [show 2 * (-bohrPoly D Z t / (4 * (B + 1))) * B =
      -bohrPoly D Z t * (B / (2 * (B + 1))) by field_simp; ring]
    have hfrac : B / (2 * (B + 1)) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    nlinarith
  linarith

/-! ### The characterization -/

/-- **Finite boundary divisors.** For a finite configuration, positive definiteness is equivalent
to nonnegativity of the Bohr polynomial. -/
theorem finiteConfig_isEvenPosDef_iff {D : ℝ → ℝ} {Z : Finset ℝ} (hD : IsFiniteConfig D Z) :
    IsEvenPosDef D ↔ ∀ t, 0 ≤ bohrPoly D Z t :=
  ⟨fun hpd => bohrPoly_nonneg hD hpd, fun hP => (bohr_isBoundaryDivisor hD hP).isEvenPosDef⟩

/-- **Boundary divisors with finite support.** A finite configuration is the boundary divisor of
some family of nonnegative weights iff its Bohr polynomial is nonnegative, iff it is the boundary
divisor of an Euler product with nonnegative integer exponents. -/
theorem finite_boundary_divisor_iff {D : ℝ → ℝ} {Z : Finset ℝ} (hD : IsFiniteConfig D Z) :
    ((∃ (ι : Type) (lam : ι → ℝ) (w : ℝ → ι → ℝ), IsBoundaryDivisor lam w D) ↔
        ∀ t, 0 ≤ bohrPoly D Z t) ∧
      ((∃ m : ℕ → ℕ, IsBoundaryDivisor logFrequency (intWeight m) D) ↔
        ∀ t, 0 ≤ bohrPoly D Z t) := by
  have hreal : (∀ t, 0 ≤ bohrPoly D Z t) →
      ∃ m : ℕ → ℕ, IsBoundaryDivisor logFrequency (intWeight m) D := fun hP =>
    ⟨_, IsBoundaryDivisor.round (fun n => hP _)
      (fun n => (le_abs_self _).trans (abs_apPoly_le _ Z _ _))
      (bohr_isBoundaryDivisor hD hP)⟩
  refine ⟨⟨fun ⟨ι, lam, w, hw⟩ => bohrPoly_nonneg hD hw.isEvenPosDef,
    fun hP => ⟨ℕ, _, _, bohr_isBoundaryDivisor hD hP⟩⟩,
    ⟨fun ⟨m, hm⟩ => bohrPoly_nonneg hD hm.isEvenPosDef, hreal⟩⟩

end GaloisForLFunctions.MultiplicativePositivityGeometry
