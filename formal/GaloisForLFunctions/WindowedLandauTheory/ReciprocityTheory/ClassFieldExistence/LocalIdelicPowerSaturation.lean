import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PowerClassDetectionPrimes
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IdelicPowerNeighborhoods

/-! A finite local multiplicative group embeds modulo powers in the
compact idelic quotient modulo the closure of its powers. -/

noncomputable section

open NumberField IsDedekindDomain GaloisForLFunctions Topology

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable {K : Type} [Field K] [NumberField K]

private theorem ord_pow_aux (v : HeightOneSpectrum (𝓞 K)) (z : IdeleGroup K) (n : ℕ) :
    ord v (z ^ n) = (n : ℤ) * ord v z := by
  induction n with
  | zero => rw [pow_zero, ord_one, Nat.cast_zero, zero_mul]
  | succ n ih => rw [pow_succ, ord_mul, ih, Nat.cast_succ, add_mul, one_mul]

private theorem finiteProj_archPositive {c : IdeleGroup K} (hc : c ∈ archPositive K)
    (w : HeightOneSpectrum (𝓞 K)) : finiteProj w c = 1 := by
  apply Units.ext
  exact congrArg (fun a : (FiniteAdeleRing (𝓞 K) K)ˣ => a.val w)
    (show toFinite K c = 1 from hc.1)

theorem finiteEmbedding_class_mem_closure_powers_iff
    {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    toCompactIdeleClassQuotient K (finiteEmbedding v x) ∈ (compactIdelePowers K n).topologicalClosure ↔
      x ∈ (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range := by
  classical
  constructor
  · intro hx
    obtain ⟨S, hvS, hS⟩ := exists_finset_principal_outside K {v}
    obtain ⟨D, hD, hdetect⟩ := Kummer.exists_finite_power_detection_primes (n := n) S {v} hS
    let P (w : HeightOneSpectrum (𝓞 K)) := (powMonoidHom n : (w.adicCompletion K)ˣ →* _).range
    let A : Set (IdeleGroup K) := {a | ∀ w, w ≠ v → ord w a = 0}
    let B := (fun a : IdeleGroup K => finiteProj v a / x) ⁻¹' (P v : Set (v.adicCompletion K)ˣ)
    let C := ⋂ w ∈ D, finiteProj w ⁻¹' (P w : Set (w.adicCompletion K)ˣ)
    have hp w : IsOpen (P w : Set (w.adicCompletion K)ˣ) :=
      isOpen_range_pow_finiteCompletion w n (NeZero.ne n)
    have hU : IsOpen (A ∩ B ∩ C) := by
      refine ((isOpen_ord_zero_away v).inter ((hp v).preimage
        ((continuous_finiteProj v).div' continuous_const))).inter ?_
      exact isOpen_biInter_finset fun w _ => (hp w).preimage (continuous_finiteProj w)
    have hxU : finiteEmbedding v x ∈ A ∩ B ∩ C := by
      refine ⟨⟨fun w hw => ord_finiteEmbedding_of_ne hw x, ?_⟩, ?_⟩
      · change finiteProj v (finiteEmbedding v x) / x ∈ P v
        rw [finiteProj_finiteEmbedding, div_self']
        exact one_mem _
      · refine Set.mem_iInter₂.mpr fun w hw => ?_
        have hw' : w ≠ v := fun h => (Finset.disjoint_left.mp hD hw) (Finset.mem_singleton.mpr h)
        change finiteProj w (finiteEmbedding v x) ∈ P w
        rw [finiteProj_finiteEmbedding_of_ne hw']
        exact one_mem _
    obtain ⟨a, c, z, hc, hY⟩ :=
      exists_diagonal_arch_mul_pow_mem_of_class_mem_closure_powers hx hU hxU
    let Y := (diagonal K a * c) * z ^ n
    have hproj (w) : finiteProj w Y = finiteProj w (diagonal K a) * finiteProj w z ^ n := by
      change finiteProj w ((diagonal K a * c) * z ^ n) = _
      rw [map_mul, map_mul, finiteProj_archPositive hc, mul_one, map_pow]
    have hdiv (w) (hw : w ∉ S) : (n : ℤ) ∣ ordAt K w (Additive.ofMul a) := by
      have hw' : w ≠ v := fun h => hw (h.symm ▸ hvS (Finset.mem_singleton_self v))
      have e := hY.1.1 w hw'
      have h0 : ord w c = 0 := by
        rw [ord, ← coe_finiteProj, finiteProj_archPositive hc, Units.val_one,
          map_one, WithZero.log_one, neg_zero]
      rw [ord_mul, ord_mul, h0, add_zero, ord_pow_aux, ord_diagonal,
        valuation_eq_exp_neg_ordAt K w a, WithZero.log_exp, neg_neg] at e
      exact ⟨-ord w z, by rw [mul_neg]; exact eq_neg_of_add_eq_zero_left e⟩
    have hloc (w) (hw : w ∈ D) : ∃ u : w.adicCompletion K, u ^ n = algebraMap K _ (a : K) := by
      have h : finiteProj w Y ∈ P w := Set.mem_iInter₂.mp hY.2 w hw
      have hz : finiteProj w z ^ n ∈ P w := ⟨finiteProj w z, rfl⟩
      have hd := (P w).div_mem h hz
      rw [hproj, mul_div_cancel_right] at hd
      obtain ⟨u, hu⟩ := hd
      exact ⟨u.val, congrArg Units.val hu⟩
    obtain ⟨b, rfl⟩ := hdetect a hdiv hloc
    have hlocal : finiteProj v Y ∈ P v := by
      rw [hproj, map_pow, map_pow, ← mul_pow]
      exact ⟨finiteProj v (diagonal K b) * finiteProj v z, rfl⟩
    have h := (P v).div_mem hlocal hY.1.2
    rwa [div_div_cancel] at h
  · rintro ⟨y, rfl⟩
    apply (compactIdelePowers K n).le_topologicalClosure
    refine ⟨toCompactIdeleClassQuotient K (finiteEmbedding v y), ?_⟩
    change _ ^ n = toCompactIdeleClassQuotient K (finiteEmbedding v (y ^ n))
    rw [map_pow, map_pow]

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteEmbedding_class_mem_closure_powers_iff
