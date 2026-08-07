import GaloisForLFunctions.HTGeometry.TripticOrbitResidueReciprocity

/-!
# The integral source divisor of a triptic multiplicative class

The zero/pole order of the shift quotient `Y(·+σ)/Y` at a point is the integer

`shiftOrder Y σ w = ord (Y, w + σ) - ord (Y, w)`,

and summing it along a `σ`-orbit gives the `τ`-side orbital divisor of the card.  This file records
the two structural facts that make that assignment a divisor homomorphism: it is additive under
multiplication of sources, and it is invariant under the integer period, so the orbital sum depends
only on the orbit.

Reciprocity (proved separately) makes the `τ`-side and `σ`-side orbital sums equal, so the two
noncommensurable elliptic realizations produce one integer-valued function on orbits.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-- The zero/pole order of the shift quotient `Y(·+σ)/Y` at a point. -/
noncomputable def shiftOrder (Y : ℂ → ℂ) (σ : ℂ) (w : ℂ) : ℤ :=
  (meromorphicOrderAt Y (w + σ)).untop₀ - (meromorphicOrderAt Y w).untop₀

/-- **The order of a product is the sum of the orders**, in the untopped integer form available
when neither factor vanishes identically near the point. -/
theorem untop₀_meromorphicOrderAt_mul {Y₁ Y₂ : ℂ → ℂ} {w : ℂ}
    (h₁ : MeromorphicAt Y₁ w) (h₂ : MeromorphicAt Y₂ w)
    (hf₁ : meromorphicOrderAt Y₁ w ≠ ⊤) (hf₂ : meromorphicOrderAt Y₂ w ≠ ⊤) :
    (meromorphicOrderAt (fun z => Y₁ z * Y₂ z) w).untop₀
      = (meromorphicOrderAt Y₁ w).untop₀ + (meromorphicOrderAt Y₂ w).untop₀ := by
  obtain ⟨n₁, hn₁⟩ := WithTop.ne_top_iff_exists.mp hf₁
  obtain ⟨n₂, hn₂⟩ := WithTop.ne_top_iff_exists.mp hf₂
  have hmul : meromorphicOrderAt (fun z => Y₁ z * Y₂ z) w
      = meromorphicOrderAt Y₁ w + meromorphicOrderAt Y₂ w := meromorphicOrderAt_mul h₁ h₂
  rw [hmul, ← hn₁, ← hn₂]
  simp

/-- **The shift order is additive under multiplication of sources.** -/
theorem shiftOrder_mul {Y₁ Y₂ : ℂ → ℂ} {σ : ℂ}
    (h₁ : MeromorphicOn Y₁ Set.univ) (h₂ : MeromorphicOn Y₂ Set.univ)
    (hf₁ : ∀ w : ℂ, meromorphicOrderAt Y₁ w ≠ ⊤) (hf₂ : ∀ w : ℂ, meromorphicOrderAt Y₂ w ≠ ⊤)
    (w : ℂ) :
    shiftOrder (fun z => Y₁ z * Y₂ z) σ w = shiftOrder Y₁ σ w + shiftOrder Y₂ σ w := by
  simp only [shiftOrder]
  rw [untop₀_meromorphicOrderAt_mul (h₁ _ (Set.mem_univ _)) (h₂ _ (Set.mem_univ _))
      (hf₁ _) (hf₂ _),
    untop₀_meromorphicOrderAt_mul (h₁ w (Set.mem_univ w)) (h₂ w (Set.mem_univ w))
      (hf₁ w) (hf₂ w)]
  ring

/-- The order is invariant under a period of the source. -/
theorem untop₀_meromorphicOrderAt_period {Y : ℂ → ℂ} {h : ℂ}
    (hper : ∀ z : ℂ, Y (z + h) = Y z) (w : ℂ) :
    (meromorphicOrderAt Y (w + h)).untop₀ = (meromorphicOrderAt Y w).untop₀ := by
  have hfun : (fun z : ℂ => Y (z + h)) = Y := funext hper
  rw [← meromorphicOrderAt_comp_add Y w h, hfun]

/-- **The shift order is invariant under a period of the source.** -/
theorem shiftOrder_period {Y : ℂ → ℂ} {σ h : ℂ}
    (hper : ∀ z : ℂ, Y (z + h) = Y z) (w : ℂ) :
    shiftOrder Y σ (w + h) = shiftOrder Y σ w := by
  simp only [shiftOrder]
  rw [show w + h + σ = w + σ + h from by ring,
    untop₀_meromorphicOrderAt_period hper (w + σ),
    untop₀_meromorphicOrderAt_period hper w]


/-- Casting an integer-valued unrestricted sum into `ℂ`. -/
theorem intCast_finsum (d : ℤ → ℤ) :
    ((∑ᶠ m : ℤ, d m : ℤ) : ℂ) = ∑ᶠ m : ℤ, ((d m : ℤ) : ℂ) :=
  (Int.castAddHom ℂ).map_finsum_of_injective Int.cast_injective d

/-- **Multiplicative triptic reciprocity in the integral channel.**  The two orbital divisors of
the shift quotients agree as integers, not merely after complexification — which is the channel the
Kummer-content classification needs. -/
theorem triptic_multiplicative_divisor_reciprocity_int
    {Y : ℂ → ℂ} {τ σ : ℂ}
    (hY : MeromorphicOn Y Set.univ)
    (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤)
    (hYper : ∀ z : ℂ, Y (z + 1) = Y z)
    {Cst : ℂ} (hmixed : ∀ z : ℂ, logDeriv Y (z + τ + σ) - logDeriv Y (z + τ)
      - logDeriv Y (z + σ) + logDeriv Y z = Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (p : ℂ) :
    ∑ᶠ m : ℤ, shiftOrder Y σ (p + (m : ℂ) * σ)
      = ∑ᶠ n : ℤ, shiftOrder Y τ (p + (n : ℂ) * τ) := by
  have hC := triptic_multiplicative_divisor_reciprocity hY hfin hYper hmixed hτ hσ hindep p
  refine Int.cast_injective (α := ℂ) ?_
  rw [intCast_finsum, intCast_finsum]
  simpa only [shiftOrder, Int.cast_sub] using hC


/-- The principal-part coefficient of a shifted logarithmic difference is the shift order. -/
theorem laurentCoeff_shiftDiff_logDeriv {Y : ℂ → ℂ} (hY : MeromorphicOn Y Set.univ)
    (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤) (h w : ℂ) :
    laurentCoeff (fun z => logDeriv Y (z + h) - logDeriv Y z) w (-1)
      = (shiftOrder Y h w : ℂ) := by
  have hlogmero : MeromorphicOn (logDeriv Y) Set.univ := fun z _ =>
    ((hY z (Set.mem_univ z)).deriv).div (hY z (Set.mem_univ z))
  rw [laurentCoeff_shiftDiff hlogmero h w (-1),
    laurentCoeff_logDeriv_eq_untop hY hfin, laurentCoeff_logDeriv_eq_untop hY hfin, shiftOrder]
  push_cast
  ring

/-- **The orbital divisor has finite support.**  Only finitely many members of a `σ`-orbit carry a
nonzero shift order. -/
theorem finite_support_shiftOrder {Y : ℂ → ℂ} {τ σ : ℂ}
    (hY : MeromorphicOn Y Set.univ) (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤)
    (hYper : ∀ z : ℂ, Y (z + 1) = Y z)
    {Cst : ℂ} (hmixed : ∀ z : ℂ, logDeriv Y (z + τ + σ) - logDeriv Y (z + τ)
      - logDeriv Y (z + σ) + logDeriv Y z = Cst)
    (hτ : 0 < τ.im)
    (hindep : ∀ m n j : ℤ, (m : ℂ) * σ + (n : ℂ) * τ + (j : ℂ) = 0 → m = 0 ∧ n = 0 ∧ j = 0)
    (p : ℂ) :
    {m : ℤ | shiftOrder Y σ (p + (m : ℂ) * σ) ≠ 0}.Finite := by
  classical
  set G : ℂ → ℂ := fun z => logDeriv Y (z + σ) - logDeriv Y z with hG
  have hlogmero : MeromorphicOn (logDeriv Y) Set.univ := fun z _ =>
    ((hY z (Set.mem_univ z)).deriv).div (hY z (Set.mem_univ z))
  have hGmero : MeromorphicOn G Set.univ := fun z _ =>
    (meromorphicAt_comp_add.mpr (hlogmero (z + σ) (Set.mem_univ _))).sub
      (hlogmero z (Set.mem_univ z))
  have hper : ∀ z : ℂ, logDeriv Y (z + 1) = logDeriv Y z := by
    intro z
    have hfun : (fun w : ℂ => Y (w + 1)) = Y := funext hYper
    have hd : deriv Y (z + 1) = deriv Y z := by
      have hcomp := deriv_comp_add_const (f := Y) (a := (1 : ℂ)) z
      rw [hfun] at hcomp
      exact hcomp.symm
    rw [logDeriv_apply, logDeriv_apply, hd, hYper z]
  have hGper1 : ∀ a : ℂ, laurentCoeff G (a + 1) (-1) = laurentCoeff G a (-1) := by
    intro a
    have hfun : (fun z : ℂ => logDeriv Y (z + 1 + σ) - logDeriv Y (z + 1)) = G := by
      funext z
      rw [hG, show z + 1 + σ = z + σ + 1 from by ring, hper (z + σ), hper z]
    calc laurentCoeff G (a + 1) (-1)
        = laurentCoeff (fun z => G (z + 1)) a (-1) := (laurentCoeff_comp_add G a 1 (-1)).symm
      _ = laurentCoeff G a (-1) := by rw [hG]; rw [hfun]
  have hGperτ : ∀ a : ℂ, laurentCoeff G (a + τ) (-1) = laurentCoeff G a (-1) := by
    intro a
    have hfun : (fun z : ℂ => G (z + τ)) = fun z => G z + Cst := by
      funext z
      simp only [hG]
      have hz := hmixed z
      linear_combination hz
    calc laurentCoeff G (a + τ) (-1)
        = laurentCoeff (fun z => G (z + τ)) a (-1) := (laurentCoeff_comp_add G a τ (-1)).symm
      _ = laurentCoeff (fun z => G z + Cst) a (-1) := by rw [hfun]
      _ = laurentCoeff G a (-1) :=
          laurentCoeff_add_const (hGmero a (Set.mem_univ a)) Cst (by norm_num)
  have hfinset := finite_setOf_laurentCoeff_ne_zero_orbit hGmero (by norm_num : (-1 : ℤ) < 0)
    hτ hGper1 hGperτ hindep p
  refine hfinset.subset ?_
  intro m hm
  simp only [Set.mem_setOf_eq] at hm ⊢
  rw [hG, laurentCoeff_shiftDiff_logDeriv hY hfin]
  exact_mod_cast hm


/-- The integral orbital charge of a source along a `σ`-orbit. -/
noncomputable def tripticOrbitCharge (Y : ℂ → ℂ) (σ p : ℂ) : ℤ :=
  ∑ᶠ m : ℤ, shiftOrder Y σ (p + (m : ℂ) * σ)

/-- **The orbital charge is additive under multiplication of sources.**  This is what makes the
common integral divisor a homomorphism, the hypothesis of the abstract Kummer classification. -/
theorem tripticOrbitCharge_mul {Y₁ Y₂ : ℂ → ℂ} {σ p : ℂ}
    (h₁ : MeromorphicOn Y₁ Set.univ) (h₂ : MeromorphicOn Y₂ Set.univ)
    (hf₁ : ∀ w : ℂ, meromorphicOrderAt Y₁ w ≠ ⊤) (hf₂ : ∀ w : ℂ, meromorphicOrderAt Y₂ w ≠ ⊤)
    (hs₁ : {m : ℤ | shiftOrder Y₁ σ (p + (m : ℂ) * σ) ≠ 0}.Finite)
    (hs₂ : {m : ℤ | shiftOrder Y₂ σ (p + (m : ℂ) * σ) ≠ 0}.Finite) :
    tripticOrbitCharge (fun z => Y₁ z * Y₂ z) σ p
      = tripticOrbitCharge Y₁ σ p + tripticOrbitCharge Y₂ σ p := by
  classical
  have hpt : ∀ m : ℤ, shiftOrder (fun z => Y₁ z * Y₂ z) σ (p + (m : ℂ) * σ)
      = shiftOrder Y₁ σ (p + (m : ℂ) * σ) + shiftOrder Y₂ σ (p + (m : ℂ) * σ) := fun m =>
    shiftOrder_mul h₁ h₂ hf₁ hf₂ _
  simp only [tripticOrbitCharge]
  rw [finsum_congr hpt]
  exact finsum_add_distrib hs₁ hs₂

/-- **The orbital charge is invariant along the orbit direction.** -/
theorem tripticOrbitCharge_shift (Y : ℂ → ℂ) (σ p : ℂ) :
    tripticOrbitCharge Y σ (p + σ) = tripticOrbitCharge Y σ p := by
  classical
  simp only [tripticOrbitCharge]
  have hshift : ∀ m : ℤ, p + σ + (m : ℂ) * σ = p + ((m + 1 : ℤ) : ℂ) * σ := by
    intro m
    push_cast
    ring
  calc ∑ᶠ m : ℤ, shiftOrder Y σ (p + σ + (m : ℂ) * σ)
      = ∑ᶠ m : ℤ, shiftOrder Y σ (p + ((m + 1 : ℤ) : ℂ) * σ) := finsum_congr (fun m => by
        rw [hshift m])
    _ = ∑ᶠ m : ℤ, shiftOrder Y σ (p + (m : ℂ) * σ) :=
        finsum_comp_equiv (e := Equiv.addRight (1 : ℤ))
          (f := fun m : ℤ => shiftOrder Y σ (p + (m : ℂ) * σ))

end GaloisForLFunctions.HTGeometry
