import Cay.Basic

/-!
A minimal smoke test target for the project.
`lake test` will typecheck this file.
-/

namespace Cay

example : (1 : Nat) + 1 = 2 := rfl

-- Some very simple property proof as a safe sanity check.
example (a : Nat) : a + 0 = a := Nat.add_zero _

end Cay
