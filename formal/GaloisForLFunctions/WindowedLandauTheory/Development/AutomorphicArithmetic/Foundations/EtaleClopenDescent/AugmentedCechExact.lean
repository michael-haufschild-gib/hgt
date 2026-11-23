import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedCechComplex
import GaloisForLFunctions.HTGeometry.FinsetCechDatum

/-! Exactness transfers from an augmented Čech datum to its
realization by submodules of one ambient module. -/

noncomputable section

open HTGeometry GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {k ι M : Type} [Field k] [LinearOrder ι] [AddCommGroup M] [Module k M]

/-- A compatible realization of Čech sections as submodules of a
common module carries augmented exactness to the alternating complex. -/
theorem acx_exact_of_cechDatum (D : FinsetCechDatum.{0} ι)
    (A : Finset ι → Submodule k M) (e : ∀ I, D.obj I ≃+ A I)
    (he : ∀ {I J} (h : I ⊆ J) (x : D.obj I),
      (e J (D.res h x) : M) = (e I x : M))
    (hbot : D.ExactBot) (hex : ∀ p, D.ExactAt p) (n : ℤ) :
    (acx A 1).Z n ≤ (acx A 1).B n := by
  intro c hc
  have hmem (I : Finset ι) : c I ∈ (if (I.card : ℤ) = n then A I else ⊥) :=
    Submodule.mem_pi.mp hc.1 I (Set.mem_univ _)
  have hs (I : Finset ι) (hI : (I.card : ℤ) ≠ n) : c I = 0 := (Submodule.mem_bot k).mp
    (by simpa only [if_neg hI] using hmem I)
  have hA (I : Finset ι) : c I ∈ A I := by
    by_cases hI : (I.card : ℤ) = n
    · simpa only [if_pos hI] using hmem I
    · rw [hs I hI]
      exact zero_mem _
  let embed (a : D.Cochain) (I : Finset ι) : M := e I (a I)
  have embed_d (a : D.Cochain) : embed (D.d a) = deltaL k ι M (embed a) := by
    funext I
    rw [deltaL_apply]
    simp only [embed, FinsetCechDatum.d, map_sum, map_zsmul, Submodule.coe_sum,
      Submodule.coe_smul_of_tower, he]
    rfl
  let c' (I : Finset ι) : D.obj I := (e I).symm ⟨c I, hA I⟩
  have h' : embed c' = c := funext fun I => congrArg Subtype.val ((e I).apply_symm_apply ⟨_, _⟩)
  have h'₀ (I : Finset ι) (hI : (I.card : ℤ) ≠ n) : c' I = 0 := by
    change (e I).symm ⟨c I, hA I⟩ = 0
    rw [show (⟨c I, hA I⟩ : A I) = 0 from Subtype.ext (hs I hI), map_zero]
  have hz : D.d c' = 0 := by
    have hz' : wd (1 : ι → Module.End k M) c = 0 := hc.2
    have e0 : embed (D.d c') = 0 := by rw [embed_d, h', ← wd_one, hz']
    funext I
    apply (e I).injective
    rw [map_zero]
    exact Subtype.ext (congrFun e0 I)
  by_cases hn : n < 0
  · have h : c = 0 := funext fun I => hs I (by omega)
    rw [h]
    exact zero_mem _
  by_cases h0 : n = 0
  · have hc₀ : c' = 0 := hbot c' (fun I hI => h'₀ I (by
      have hpos := Finset.card_pos.mpr hI
      omega)) hz
    have h : c = 0 := h'.symm.trans (by rw [hc₀]; funext I; simp [embed])
    rw [h]
    exact zero_mem _
  let p := n.toNat - 1
  have hp : n = (p : ℤ) + 1 := by dsimp [p]; omega
  obtain ⟨b, hb, hdb⟩ := hex p c' (fun I hi => h'₀ I (by omega)) hz
  refine ⟨embed b, Submodule.mem_pi.mpr (fun I _ => ?_), ?_⟩
  · change embed b I ∈ (if (I.card : ℤ) = n - 1 then A I else ⊥)
    split_ifs with hi
    · exact (e I (b I)).2
    · have hb₀ := hb I (by omega)
      simp only [embed, hb₀, map_zero, Submodule.coe_zero, Submodule.mem_bot]
  · change wd (1 : ι → Module.End k M) (embed b) = c
    rw [wd_one, ← embed_d, hdb, h']

end GlobalTheory.WH
