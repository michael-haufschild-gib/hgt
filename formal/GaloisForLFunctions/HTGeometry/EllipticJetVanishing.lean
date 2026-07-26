import GaloisForLFunctions.HTGeometry.EllipticCountingTools

/-!
# Vanishing principal jets mean no pole

The counting argument produces a combination whose principal-part coefficients all vanish.  This
file turns that into the statement that the combination has no pole: if the first `d` jets of the
cleared function `(· − p)^d · g` vanish at `p`, then that cleared function has a zero of order at
least `d` there, so the factor `(· − p)^d` is entirely absorbed and the order of `g` itself is
nonnegative.

The bridge is mathlib's `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`, which is exactly the
Taylor-coefficient characterisation of the order of a zero, together with the order computation
`meromorphicOrderAt_poleFactor_mul`.

* **`nonneg_order_of_principalJet_eq_zero`** — vanishing principal jets force a nonnegative order.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Vanishing principal jets mean no pole.**  If the principal-part coefficients of `g` at `p`
relative to the clearing exponent `d` all vanish, then `g` has nonnegative order at `p`. -/
theorem nonneg_order_of_principalJet_eq_zero {g : ℂ → ℂ} {p : ℂ} {d : ℕ}
    (hg : MeromorphicAt g p)
    (hmer : MeromorphicOn (fun z => (z - p) ^ d * g z) Set.univ)
    (hord : 0 ≤ meromorphicOrderAt (fun z => (z - p) ^ d * g z) p)
    (hjet : ∀ k, k < d → principalJet g p d k = 0) :
    0 ≤ meromorphicOrderAt g p := by
  have hA : AnalyticAt ℂ (poleClear g p d) p := analyticAt_poleClear hmer hord
  have hge : (d : ℕ∞) ≤ analyticOrderAt (poleClear g p d) p := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA]
    intro i hi
    have hid : i < d := by exact_mod_cast hi
    exact hjet i hid
  have hmero : meromorphicOrderAt (poleClear g p d) p
      = (analyticOrderAt (poleClear g p d) p).map (↑) := hA.meromorphicOrderAt_eq
  have hd_le : ((d : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (poleClear g p d) p := by
    rw [hmero]
    have hmono : Monotone (ENat.map (Nat.cast : ℕ → ℤ)) :=
      ENat.monotone_map_iff.mpr (fun a b hab => by exact_mod_cast hab)
    have hmapped := hmono hge
    have hdmap : ENat.map (Nat.cast : ℕ → ℤ) (d : ℕ∞) = ((d : ℤ) : WithTop ℤ) := by simp
    rwa [hdmap] at hmapped
  have heq : meromorphicOrderAt (poleClear g p d) p
      = (d : WithTop ℤ) + meromorphicOrderAt g p := by
    rw [poleClear, meromorphicOrderAt_toMeromorphicNFOn hmer (Set.mem_univ p),
      meromorphicOrderAt_poleFactor_mul hg]
  rw [heq] at hd_le
  rcases eq_or_ne (meromorphicOrderAt g p) ⊤ with htop | hne
  · rw [htop]
    exact le_top
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hk] at hd_le ⊢
    have hsum : (d : WithTop ℤ) + (k : WithTop ℤ) = (((d : ℤ) + k : ℤ) : WithTop ℤ) := by
      norm_cast
    rw [hsum] at hd_le
    have hint : (d : ℤ) ≤ (d : ℤ) + k := by exact_mod_cast hd_le
    have hk0 : (0 : ℤ) ≤ k := by omega
    exact_mod_cast hk0

end GaloisForLFunctions.HTGeometry
