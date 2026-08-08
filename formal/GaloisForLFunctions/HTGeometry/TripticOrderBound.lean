import GaloisForLFunctions.HTGeometry.TripticLineSupportFinite
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentOrderVanishing

/-!
# The column field is a row field, and only finitely many orders occur

Two facts complete the finiteness of the normal-form index set.

First, the backward column sum is the forward row sum in the other direction: the total transverse
mass vanishes, so `colCoeff F σ ℓ = rowCoeff F σ ℓ`.  Everything can therefore be phrased with the
row field alone, once in each of the two lattice directions.

Second, the orders are bounded.  A nonzero row coefficient at order `ℓ` forces a pole of the boundary
function with a nonzero coefficient at that index, hence of order at most `ℓ`; the poles reduce to a
finite list of classes whose orders agree with theirs, and the least of those orders bounds `ℓ` from
below.

* `colCoeff_eq_rowCoeff`;
* `meromorphicOrderAt_eq_of_laurentCoeff_eq` — the order is read off the principal part;
* `exists_order_bound_rowCoeff`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

noncomputable section

variable {F : ℂ → ℂ} {τ σ : ℂ}

/-- **The column field is the row field in the other direction.** -/
theorem colCoeff_eq_rowCoeff {ℓ : ℤ} {w : ℂ}
    (hfin : {n : ℤ | laurentCoeff (fun z => F (z + σ) - F z) (w + (n : ℂ) * σ) ℓ ≠ 0}.Finite)
    (hzero : ∑ᶠ n : ℤ, laurentCoeff (fun z => F (z + σ) - F z) (w + (n : ℂ) * σ) ℓ = 0) :
    colCoeff F σ ℓ w = rowCoeff F σ ℓ w :=
  (rowCoeff_eq_backward_sum hfin hzero).symm

/-- **The order is determined by the principal part.**  Two germs with the same negative Laurent
coefficients and both polar have the same order. -/
theorem meromorphicOrderAt_eq_of_laurentCoeff_eq {f : ℂ → ℂ} {a b : ℂ}
    (hfa : MeromorphicAt f a) (hfb : MeromorphicAt f b)
    (hcoeff : ∀ ℓ : ℤ, ℓ < 0 → laurentCoeff f a ℓ = laurentCoeff f b ℓ)
    (ha : meromorphicOrderAt f a < 0) :
    meromorphicOrderAt f a = meromorphicOrderAt f b := by
  have hane : meromorphicOrderAt f a ≠ ⊤ := by
    intro htop
    rw [htop] at ha
    exact absurd ha (by simp)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hane
  have hneg : n < 0 := by
    rw [← hn] at ha
    exact_mod_cast ha
  have hlead : laurentCoeff f a n ≠ 0 := laurentCoeff_leading_ne_zero hneg hfa hn.symm
  have hleadb : laurentCoeff f b n ≠ 0 := by
    rw [← hcoeff n hneg]
    exact hlead
  have hble : meromorphicOrderAt f b ≤ (n : WithTop ℤ) :=
    meromorphicOrderAt_le_of_laurentCoeff_ne_zero hfb hleadb
  have hbneg : meromorphicOrderAt f b < 0 :=
    lt_of_le_of_lt hble (by exact_mod_cast hneg)
  have hbne : meromorphicOrderAt f b ≠ ⊤ := by
    intro htop
    rw [htop] at hbneg
    exact absurd hbneg (by simp)
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hbne
  have hmneg : m < 0 := by
    rw [← hm] at hbneg
    exact_mod_cast hbneg
  have hleadm : laurentCoeff f b m ≠ 0 := laurentCoeff_leading_ne_zero hmneg hfb hm.symm
  have hleadma : laurentCoeff f a m ≠ 0 := by
    rw [hcoeff m hmneg]
    exact hleadm
  have hale : meromorphicOrderAt f a ≤ (m : WithTop ℤ) :=
    meromorphicOrderAt_le_of_laurentCoeff_ne_zero hfa hleadma
  have h1 : n ≤ m := by
    rw [← hn] at hale
    exact_mod_cast hale
  have h2 : m ≤ n := by
    rw [← hm] at hble
    exact_mod_cast hble
  rw [← hn, ← hm]
  exact_mod_cast le_antisymm h1 h2

/-- **Only finitely many orders carry a nonzero row coefficient.** -/
theorem exists_order_bound_rowCoeff
    (hV : MeromorphicOn (fun z => F (z + τ) - F z) Set.univ)
    (hindepR : LinearIndependent ℝ ![(1 : ℂ), σ])
    (hVper1 : ∀ (ℓ' : ℤ), ℓ' < 0 → ∀ a : ℂ,
      laurentCoeff (fun z => F (z + τ) - F z) (a + 1) ℓ'
        = laurentCoeff (fun z => F (z + τ) - F z) a ℓ')
    (hVperσ : ∀ (ℓ' : ℤ), ℓ' < 0 → ∀ a : ℂ,
      laurentCoeff (fun z => F (z + τ) - F z) (a + σ) ℓ'
        = laurentCoeff (fun z => F (z + τ) - F z) a ℓ') :
    ∃ J : ℤ, ∀ (ℓ : ℤ), ℓ < J → ∀ w : ℂ, rowCoeff F τ ℓ w = 0 := by
  classical
  set V : ℂ → ℂ := fun z => F (z + τ) - F z with hVdef
  have hlat : ∀ (m n : ℤ) (z : ℂ) (ℓ' : ℤ), ℓ' < 0 →
      laurentCoeff V (z - (m • (1 : ℂ) + n • σ)) ℓ' = laurentCoeff V z ℓ' := by
    intro m n z ℓ' hℓ'
    have h1 : laurentCoeff V ((z - (m • (1 : ℂ) + n • σ)) + ((m : ℂ) * 1)) ℓ'
        = laurentCoeff V (z - (m • (1 : ℂ) + n • σ)) ℓ' :=
      laurentCoeff_add_zsmul_of_period (hVper1 ℓ' hℓ') _ m
    have h2 : laurentCoeff V ((z - (m • (1 : ℂ) + n • σ)) + ((m : ℂ) * 1) + ((n : ℂ) * σ)) ℓ'
        = laurentCoeff V ((z - (m • (1 : ℂ) + n • σ)) + ((m : ℂ) * 1)) ℓ' :=
      laurentCoeff_add_zsmul_of_period (hVperσ ℓ' hℓ') _ n
    have hpt : (z - (m • (1 : ℂ) + n • σ)) + ((m : ℂ) * 1) + ((n : ℂ) * σ) = z := by
      simp only [zsmul_eq_mul]
      ring
    rw [hpt] at h2
    rw [← h1, ← h2]
  have hstep : ∀ (m n : ℤ) (z : ℂ), meromorphicOrderAt V z < 0 →
      meromorphicOrderAt V (z - (m • (1 : ℂ) + n • σ)) < 0 := by
    intro m n z hz
    obtain ⟨ℓ', hℓ', hne⟩ :=
      (meromorphicOrderAt_neg_iff_exists_laurentCoeff_ne_zero (hV z (Set.mem_univ z))).mp hz
    refine (meromorphicOrderAt_neg_iff_exists_laurentCoeff_ne_zero
      (hV _ (Set.mem_univ _))).mpr ⟨ℓ', hℓ', ?_⟩
    rw [hlat m n z ℓ' hℓ']
    exact hne
  obtain ⟨P, hP⟩ := exists_finset_pole_classes hV hindepR hstep
  set J : ℤ := -((P.sup fun q => (meromorphicOrderAt V q).untop₀.natAbs : ℕ) : ℤ) with hJ
  refine ⟨J, fun ℓ hℓJ w => ?_⟩
  by_contra hne
  obtain ⟨k, hk⟩ := exists_ne_zero_of_rowCoeff_ne_zero hne
  have hℓneg : ℓ < 0 := by
    by_contra hpos
    have hnn : 0 ≤ meromorphicOrderAt V (w + ((k : ℤ) : ℂ) * τ) := by
      by_contra hlt
      have := (meromorphicOrderAt_neg_iff_exists_laurentCoeff_ne_zero
        (hV _ (Set.mem_univ _))).mp (not_le.mp hlt)
      omega
    exact hk (laurentCoeff_eq_zero_of_lt_meromorphicOrderAt (hV _ (Set.mem_univ _))
      (lt_of_lt_of_le (by exact_mod_cast (by omega : ℓ < 0)) hnn))
  have hpole : meromorphicOrderAt V (w + ((k : ℤ) : ℂ) * τ) < 0 :=
    meromorphicOrderAt_neg_of_laurentCoeff_ne_zero (hV _ (Set.mem_univ _)) hℓneg hk
  obtain ⟨a, b, hq⟩ := hP _ hpole
  set q : ℂ := w + ((k : ℤ) : ℂ) * τ - (a • (1 : ℂ) + b • σ) with hqdef
  have hqorder : meromorphicOrderAt V (w + ((k : ℤ) : ℂ) * τ) = meromorphicOrderAt V q := by
    refine meromorphicOrderAt_eq_of_laurentCoeff_eq (hV _ (Set.mem_univ _))
      (hV _ (Set.mem_univ _)) (fun ℓ' hℓ' => ?_) hpole
    rw [hqdef, hlat a b _ ℓ' hℓ']
  have hqneg : meromorphicOrderAt V q < 0 := hqorder ▸ hpole
  have hqne : meromorphicOrderAt V q ≠ ⊤ := by
    intro htop
    rw [htop] at hqneg
    exact absurd hqneg (by simp)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hqne
  have hnneg : n < 0 := by
    rw [← hn] at hqneg
    exact_mod_cast hqneg
  have hle : meromorphicOrderAt V (w + ((k : ℤ) : ℂ) * τ) ≤ (ℓ : WithTop ℤ) :=
    meromorphicOrderAt_le_of_laurentCoeff_ne_zero (hV _ (Set.mem_univ _)) hk
  rw [hqorder, ← hn] at hle
  have hnl : n ≤ ℓ := by exact_mod_cast hle
  have hsup : (meromorphicOrderAt V q).untop₀.natAbs
      ≤ P.sup fun r => (meromorphicOrderAt V r).untop₀.natAbs :=
    Finset.le_sup (f := fun r => (meromorphicOrderAt V r).untop₀.natAbs) hq
  rw [← hn] at hsup
  simp only [WithTop.untop₀_coe] at hsup
  have : (n.natAbs : ℤ) ≤ ((P.sup fun r => (meromorphicOrderAt V r).untop₀.natAbs : ℕ) : ℤ) := by
    exact_mod_cast hsup
  rw [hJ] at hℓJ
  omega

end

end GaloisForLFunctions.HTGeometry
