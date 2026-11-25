import PlanarEG.CertTree

/-!
# PlanarEG.CertTree16

Zero-`Std` (pure `Init`) extension of `PlanarEG.CertTree` for `C_4, C_8, C_16`
outer-rim quotient & weld cycle witnesses (used by Stage 3 `GeneralPlanarC16` data modules
without triggering recompilation of Stage 2 `.olean` caches).
-/

namespace PlanarEG.CertTree

/-- Pure-`Nat` / `Bool` checker verifying that `cyc` is a simple cycle of length
`4`, `8`, or `16` (`HasDyadicCycleUpTo 16`) in the face graph `faces` on `n` vertices. -/
def checkWeldDyadic16 (n : Nat) (faces : List (List Nat)) (cyc : List Nat) : Bool :=
  let len := cyc.length
  (len == 4 || len == 8 || len == 16) &&
  allLtNat n cyc &&
  nodupNat cyc &&
  isFaceGraphClosedWalk faces cyc

/-- Check BOTH strict face-schema validity AND explicit simple `C_4, C_8,` or `C_16` cycle
for every `WeldWitness` in a list. -/
def checkWeldList16 : List WeldWitness → Bool
  | [] => true
  | w :: ws =>
    if checkWeldSchema w && checkWeldDyadic16 w.numVerts w.faces w.cycle then
      checkWeldList16 ws
    else false

theorem checkWeldList16_eq_true :
    ∀ {ws : List WeldWitness}, checkWeldList16 ws = true →
      ∀ w ∈ ws, checkWeldSchema w = true ∧ checkWeldDyadic16 w.numVerts w.faces w.cycle = true
  | [], _, _, hmem => by cases hmem
  | x :: xs, h, w, hmem => by
    unfold checkWeldList16 at h
    cases hx : (checkWeldSchema x && checkWeldDyadic16 x.numVerts x.faces x.cycle)
    · rw [hx] at h; cases h
    · rw [hx] at h
      cases hmem with
      | head => exact Bool.and_eq_true _ _ |>.mp hx
      | tail _ hm => exact checkWeldList16_eq_true h w hm

theorem checkWeldDyadicCycle_of_16 {n : Nat} {faces : List (List Nat)} {cyc : List Nat}
    (h : checkWeldDyadic16 n faces cyc = true) :
    checkWeldDyadicCycle n faces cyc = true := by
  unfold checkWeldDyadic16 at h
  unfold checkWeldDyadicCycle
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h ⊢
  rcases h with ⟨⟨⟨hlen, hlt⟩, hnd⟩, hwalk⟩
  exact ⟨⟨⟨Or.inl hlen, hlt⟩, hnd⟩, hwalk⟩

end PlanarEG.CertTree
