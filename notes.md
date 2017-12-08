# Notes

## `pred` - predicate
Specifies a scope that bounds the search for instances
```alloy
pred show {}
```
Contains no constraints, but
```alloy
pred show {}
run show for 3 but 1 Book
```
Runs unconstrained `show` predicate, but limits to three objects per signature, except for Book which is limited to one.
