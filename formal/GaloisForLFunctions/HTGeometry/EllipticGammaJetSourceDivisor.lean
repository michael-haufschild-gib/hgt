import GaloisForLFunctions.HTGeometry.EllipticGammaSourceOrbitalDivisor
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentJet
import GaloisForLFunctions.HTGeometry.MeromorphicLogDerivLocalForm

/-!
# The orbital divisor of a jet of the elliptic gamma source

The elliptic gamma source is a logarithmic derivative, so it has no Laurent coefficient below its
residue and its orbital divisor is carried entirely by order `-1`.  Its `j`-th jet therefore has an
orbital divisor carried entirely by order `-(j+1)`, where it is `(-1)ʲ j!` times the multiplicative
orbital charge; at every other negative order the falling product of the jet law vanishes or the
underlying source contributes nothing.

The jets of the gamma translates are thus an exact basis for prescribing an orbital divisor: one
jet per class and per order, each invisible to every other slot.

* `additiveOrbitalDivisorAt`;
* `additiveOrbitalDivisorAt_iteratedDeriv` — the jet law for orbital divisors;
* `additiveOrbitalDivisorAt_gammaJetSource_self`, `..._of_ne_order`.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The additive orbital divisor of a source at a given order along the `σ`-orbit through `p`. -/
def additiveOrbitalDivisorAt (F : ℂ → ℂ) (σ p : ℂ) (ℓ : ℤ) : ℂ :=
  ∑ᶠ m : ℤ, laurentCoeff (fun z ↦ F (z + σ) - F z) (p + (m : ℂ) * σ) ℓ

theorem additiveOrbitalDivisorAt_neg_one (F : ℂ → ℂ) (σ p : ℂ) :
    additiveOrbitalDivisorAt F σ p (-1) = additiveOrbitalDivisor F σ p := rfl

/-- **The jet law for orbital divisors.**  Differentiating a source multiplies its orbital divisor
by the falling product and shifts the order. -/
theorem additiveOrbitalDivisorAt_iteratedDeriv {F : ℂ → ℂ}
    (hF : MeromorphicOn F (Set.univ : Set ℂ)) (σ p : ℂ) (j : ℕ) (ℓ : ℤ) :
    additiveOrbitalDivisorAt (iteratedDeriv j F) σ p ℓ
      = (∏ i ∈ Finset.range j, ((ℓ : ℂ) + (i : ℂ) + 1))
        * additiveOrbitalDivisorAt F σ p (ℓ + (j : ℤ)) := by
  have hjet : MeromorphicOn (iteratedDeriv j F) (Set.univ : Set ℂ) := fun z _ ↦
    meromorphicAt_iteratedDeriv (hF z (Set.mem_univ z)) j
  have hterm : ∀ m : ℤ,
      laurentCoeff (fun z ↦ iteratedDeriv j F (z + σ) - iteratedDeriv j F z)
          (p + (m : ℂ) * σ) ℓ
        = (∏ i ∈ Finset.range j, ((ℓ : ℂ) + (i : ℂ) + 1))
          * laurentCoeff (fun z ↦ F (z + σ) - F z) (p + (m : ℂ) * σ) (ℓ + (j : ℤ)) := by
    intro m
    rw [laurentCoeff_shiftDiff hjet σ _ ℓ, laurentCoeff_shiftDiff hF σ _ (ℓ + (j : ℤ)),
      laurentCoeff_iteratedDeriv_eq (hF _ (Set.mem_univ _)) j ℓ,
      laurentCoeff_iteratedDeriv_eq (hF _ (Set.mem_univ _)) j ℓ]
    ring
  rw [additiveOrbitalDivisorAt, additiveOrbitalDivisorAt, finsum_congr hterm]
  exact (mul_finsum _ _).symm

/-- The `j`-th jet of the translated elliptic gamma source. -/
def gammaJetSource (a b g : ℂ) (j : ℕ) : ℂ → ℂ :=
  iteratedDeriv j (logDeriv (ellipticGammaConeTranslate a b g))

/-- A logarithmic derivative has no orbital divisor below order `-1`. -/
theorem additiveOrbitalDivisorAt_logDeriv_of_le {Y : ℂ → ℂ}
    (hY : MeromorphicOn Y (Set.univ : Set ℂ)) (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤)
    (σ p : ℂ) {ℓ : ℤ} (hℓ : ℓ ≤ -2) :
    additiveOrbitalDivisorAt (logDeriv Y) σ p ℓ = 0 := by
  have hlog : MeromorphicOn (logDeriv Y) (Set.univ : Set ℂ) := fun z _ ↦
    ((hY z (Set.mem_univ z)).deriv).div (hY z (Set.mem_univ z))
  have hterm : ∀ m : ℤ,
      laurentCoeff (fun z ↦ logDeriv Y (z + σ) - logDeriv Y z) (p + (m : ℂ) * σ) ℓ = 0 := by
    intro m
    rw [laurentCoeff_shiftDiff hlog σ _ ℓ]
    obtain ⟨n₁, hn₁⟩ := WithTop.ne_top_iff_exists.mp (hfin (p + (m : ℂ) * σ + σ))
    obtain ⟨n₂, hn₂⟩ := WithTop.ne_top_iff_exists.mp (hfin (p + (m : ℂ) * σ))
    rw [laurentCoeff_logDeriv_eq_zero_of_le (hY _ (Set.mem_univ _)) hn₁.symm hℓ,
      laurentCoeff_logDeriv_eq_zero_of_le (hY _ (Set.mem_univ _)) hn₂.symm hℓ, sub_zero]
  rw [additiveOrbitalDivisorAt, finsum_congr hterm, finsum_zero]

/-- **A gamma jet realizes its own order and nothing else.**  At order `-(j+1)` on its own class it
is `(-1)ʲ j!`. -/
theorem additiveOrbitalDivisorAt_gammaJetSource_self {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (hindep : IndepPeriods a b) (g : ℂ) (j : ℕ) :
    additiveOrbitalDivisorAt (gammaJetSource a b g j) b g (-((j : ℤ) + 1))
      = (-1) ^ j * (j.factorial : ℂ) := by
  have hmero : MeromorphicOn (logDeriv (ellipticGammaConeTranslate a b g)) (Set.univ : Set ℂ) :=
    fun z _ ↦ ((meromorphicOn_ellipticGammaConeTranslate ha hb g z (Set.mem_univ z)).deriv).div
      (meromorphicOn_ellipticGammaConeTranslate ha hb g z (Set.mem_univ z))
  rw [gammaJetSource, additiveOrbitalDivisorAt_iteratedDeriv hmero b g j,
    prod_range_neg_succ j, show -((j : ℤ) + 1) + (j : ℤ) = -1 by ring,
    additiveOrbitalDivisorAt_neg_one,
    additiveOrbitalDivisor_ellipticGammaSourceTranslate ha hb hindep g, mul_one]

/-- **A gamma jet is invisible at every other order.** -/
theorem additiveOrbitalDivisorAt_gammaJetSource_of_ne_order {a b : ℂ} (ha : 0 < a.im)
    (hb : 0 < b.im) (g p : ℂ) (j : ℕ) {i : ℕ} (hij : i ≠ j) :
    additiveOrbitalDivisorAt (gammaJetSource a b g j) b p (-((i : ℤ) + 1)) = 0 := by
  have hmero : MeromorphicOn (logDeriv (ellipticGammaConeTranslate a b g)) (Set.univ : Set ℂ) :=
    fun z _ ↦ ((meromorphicOn_ellipticGammaConeTranslate ha hb g z (Set.mem_univ z)).deriv).div
      (meromorphicOn_ellipticGammaConeTranslate ha hb g z (Set.mem_univ z))
  rw [gammaJetSource, additiveOrbitalDivisorAt_iteratedDeriv hmero b p j]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rw [prod_range_eq_zero_of_mem (j := j) (ℓ := -((i : ℤ) + 1))
      (by exact_mod_cast (by omega : -(j : ℤ) ≤ -((i : ℤ) + 1))) (by omega), zero_mul]
  · rw [additiveOrbitalDivisorAt_logDeriv_of_le
      (meromorphicOn_ellipticGammaConeTranslate ha hb g)
      (meromorphicOrderAt_ellipticGammaConeTranslate_ne_top ha hb g) b p
      (by omega : -((i : ℤ) + 1) + (j : ℤ) ≤ -2), mul_zero]

/-- The divisor of a translated gamma jet is the divisor of the untranslated one at the translated
base point. -/
theorem additiveOrbitalDivisorAt_gammaJetSource_translate (a b g p : ℂ) (j : ℕ) (ℓ : ℤ) :
    additiveOrbitalDivisorAt (gammaJetSource a b g j) b p ℓ
      = additiveOrbitalDivisorAt (gammaJetSource a b 0 j) b (p - g) ℓ := by
  have hfun : gammaJetSource a b g j = fun z ↦ gammaJetSource a b 0 j (z + -g) := by
    have hbase : ellipticGammaConeTranslate a b g
        = fun z ↦ ellipticGammaConeTranslate a b 0 (z + -g) := by
      funext z
      simp only [ellipticGammaConeTranslate]
      congr 1
      ring
    have hlog : logDeriv (ellipticGammaConeTranslate a b g)
        = fun z ↦ logDeriv (ellipticGammaConeTranslate a b 0) (z + -g) := by
      rw [hbase]
      funext z
      rw [logDeriv_apply, logDeriv_apply, deriv_comp_add_const]
    rw [gammaJetSource, gammaJetSource, hlog, iteratedDeriv_comp_add_const]
  have hterm : ∀ m : ℤ,
      laurentCoeff (fun z ↦ gammaJetSource a b g j (z + b) - gammaJetSource a b g j z)
          (p + (m : ℂ) * b) ℓ
        = laurentCoeff (fun z ↦ gammaJetSource a b 0 j (z + b) - gammaJetSource a b 0 j z)
          (p - g + (m : ℂ) * b) ℓ := by
    intro m
    have hshift : (fun z ↦ gammaJetSource a b g j (z + b) - gammaJetSource a b g j z)
        = fun z ↦ (fun w ↦ gammaJetSource a b 0 j (w + b) - gammaJetSource a b 0 j w) (z + -g) := by
      funext z
      rw [hfun]
      congr 2
      ring
    rw [hshift, laurentCoeff_comp_add
      (fun w ↦ gammaJetSource a b 0 j (w + b) - gammaJetSource a b 0 j w) (p + (m : ℂ) * b) (-g) ℓ]
    congr 1
    ring
  rw [additiveOrbitalDivisorAt, additiveOrbitalDivisorAt, finsum_congr hterm]

/-- **A gamma jet carries no divisor off the period coset of its translation point.** -/
theorem additiveOrbitalDivisorAt_gammaJetSource_of_notMem {a b : ℂ} (ha : 0 < a.im)
    (hb : 0 < b.im) {p : ℂ} (hp : ¬ PeriodGroupMem a b p) (j : ℕ) :
    additiveOrbitalDivisorAt (gammaJetSource a b 0 j) b p (-((j : ℤ) + 1)) = 0 := by
  have hzero : ellipticGammaConeTranslate a b 0 = ellipticGammaCone a b := by
    funext z
    simp [ellipticGammaConeTranslate]
  have hmero : MeromorphicOn (logDeriv (ellipticGammaCone a b)) (Set.univ : Set ℂ) :=
    fun z _ ↦ ((meromorphicOn_ellipticGammaCone ha hb z (Set.mem_univ z)).deriv).div
      (meromorphicOn_ellipticGammaCone ha hb z (Set.mem_univ z))
  rw [gammaJetSource, hzero, additiveOrbitalDivisorAt_iteratedDeriv hmero b p j,
    show -((j : ℤ) + 1) + (j : ℤ) = -1 by ring, additiveOrbitalDivisorAt_neg_one,
    additiveOrbitalDivisor_ellipticGammaSource_of_notMem ha hb hp, mul_zero]

/-- **A gamma jet carries no divisor off the class of its translation point.** -/
theorem additiveOrbitalDivisorAt_gammaJetSource_of_notMem_translate {a b : ℂ} (ha : 0 < a.im)
    (hb : 0 < b.im) {g p : ℂ} (hp : ¬ PeriodGroupMem a b (p - g)) (j : ℕ) :
    additiveOrbitalDivisorAt (gammaJetSource a b g j) b p (-((j : ℤ) + 1)) = 0 := by
  rw [additiveOrbitalDivisorAt_gammaJetSource_translate a b g p j]
  exact additiveOrbitalDivisorAt_gammaJetSource_of_notMem ha hb hp j

/-- **The additive orbital divisor of the gamma source is `1` at every period point.** -/
theorem additiveOrbitalDivisor_ellipticGammaSource_periodPoint {a b : ℂ} (ha : 0 < a.im)
    (hb : 0 < b.im) (hindep : IndepPeriods a b) (c d e : ℤ) :
    additiveOrbitalDivisor (logDeriv (ellipticGammaCone a b)) b
        ((c : ℂ) + (d : ℂ) * a + (e : ℂ) * b) = 1 := by
  rw [additiveOrbitalDivisor_logDeriv (meromorphicOn_ellipticGammaCone ha hb)
    (meromorphicOrderAt_ellipticGammaCone_ne_top ha hb) b _,
    tripticOrbitCharge_ellipticGammaCone_periodPoint ha hb hindep c d e]
  norm_num

/-- **A gamma jet realizes its own order at every point of its own class.**  This is the class
function property of the basis: the coefficient computed at the translation point cancels the
divisor at every other representative of the class simultaneously. -/
theorem additiveOrbitalDivisorAt_gammaJetSource_periodPoint {a b : ℂ} (ha : 0 < a.im)
    (hb : 0 < b.im) (hindep : IndepPeriods a b) (g : ℂ) (j : ℕ) (c d e : ℤ) :
    additiveOrbitalDivisorAt (gammaJetSource a b g j) b
        (g + ((c : ℂ) + (d : ℂ) * a + (e : ℂ) * b)) (-((j : ℤ) + 1))
      = (-1) ^ j * (j.factorial : ℂ) := by
  have hzero : ellipticGammaConeTranslate a b 0 = ellipticGammaCone a b := by
    funext z
    simp [ellipticGammaConeTranslate]
  have hmero : MeromorphicOn (logDeriv (ellipticGammaCone a b)) (Set.univ : Set ℂ) :=
    fun z _ ↦ ((meromorphicOn_ellipticGammaCone ha hb z (Set.mem_univ z)).deriv).div
      (meromorphicOn_ellipticGammaCone ha hb z (Set.mem_univ z))
  rw [additiveOrbitalDivisorAt_gammaJetSource_translate a b g _ j,
    show g + ((c : ℂ) + (d : ℂ) * a + (e : ℂ) * b) - g
      = (c : ℂ) + (d : ℂ) * a + (e : ℂ) * b by ring,
    gammaJetSource, hzero, additiveOrbitalDivisorAt_iteratedDeriv hmero b _ j,
    prod_range_neg_succ j, show -((j : ℤ) + 1) + (j : ℤ) = -1 by ring,
    additiveOrbitalDivisorAt_neg_one,
    additiveOrbitalDivisor_ellipticGammaSource_periodPoint ha hb hindep c d e, mul_one]

end

end GaloisForLFunctions.HTGeometry
